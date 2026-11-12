"""The complexity bounds of the repository: snapshots, minimisation, tables.

usage: run.py snapshot NAME [--rev REV | --root DIR] [--title T] [--description D]
       run.py minimise [--screen] [FILE...]
       run.py table [RUN...]
       run.py show [RUN...]
       run.py check [RUN]

snapshot  extract the bounds (of the working tree, of a git revision, or of
          another tree) into bounds/runs/NAME.jsonl, and add NAME to the
          manifest bounds/runs.json if needed
minimise  minimise the constants of the files of config.json ("order", or
          FILE...), in dependency order: the dependencies are built, the
          bounds minimised (minimise.py), the constants copied in several
          places minimised together (groups.py), and the file built
table     the comparison of config.json ("table"), or of RUN...
show      the same comparison as an HTML page (with a filter and sticky
          columns), written to bounds-comparison.html and opened in the
          browser
check     compare the working tree with the run RUN (default: the last of
          the manifest): fail if a bound has a higher constant or another
          shape
"""
import json, os, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compare, extract

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
CONFIG = json.load(open(os.path.join(HERE, 'config.json')))
MANIFEST = os.path.join(REPO, 'bounds', 'runs.json')

def make(target):
    return subprocess.run(['make', '-f', 'makefile.coq', target], cwd=REPO,
                          capture_output=True, text=True)

def snapshot(args):
    name = args.pop(0); opts = {}
    while args:
        o = args.pop(0); opts[o.lstrip('-')] = args.pop(0)
    entries = extract.snapshot(opts.get('root'), opts.get('rev'))
    os.makedirs(os.path.join(REPO, 'bounds', 'runs'), exist_ok=True)
    with open(os.path.join(REPO, 'bounds', 'runs', name + '.jsonl'), 'w') as f:
        for e in entries: f.write(json.dumps(e, ensure_ascii=False) + '\n')
    man = json.load(open(MANIFEST)) if os.path.exists(MANIFEST) else []
    if not any(r['name'] == name for r in man):
        man.append({'name': name, 'parent': man[-1]['name'] if man else None,
                    'title': opts.get('title', name),
                    'source': f"revision {opts['rev']}" if 'rev' in opts else 'working tree',
                    'description': opts.get('description', '')})
        json.dump(man, open(MANIFEST, 'w'), indent=2, ensure_ascii=False)
    print(f'{len(entries)} bounds -> bounds/runs/{name}.jsonl')

def minimise(args):
    screen = '--screen' in args
    files = [a for a in args if a != '--screen'] or CONFIG['order']
    tools = os.path.join(HERE)
    for f in files:
        vo = 'theories/' + f[:-2] + '.vo'
        print('===', f, flush=True)
        make(vo)                                   # dependencies (and the file, if it compiles)
        r = subprocess.run([sys.executable, os.path.join(tools, 'minimise.py')] + (['--screen'] if screen else []) + [f])
        if r.returncode: sys.exit(r.returncode)
        if f in CONFIG['groups']:
            r = subprocess.run([sys.executable, os.path.join(tools, 'groups.py')] + (['--screen'] if screen else []) + [f])
            if r.returncode: sys.exit(r.returncode)
        r = make(vo)
        if r.returncode:
            print(r.stdout[-3000:], r.stderr[-3000:]); print('=== BUILD FAILED', f); sys.exit(1)
        print('=== built', f, flush=True)

def table(args):
    t = CONFIG['table']
    runs = args or t['runs']
    compare.main(runs + ['--header', os.path.join(REPO, t['header']), '-o', os.path.join(REPO, t['output'])])
    print('table ->', t['output'])

def show(args):
    import webbrowser
    t = CONFIG['table']
    runs = args or t['runs']
    out = os.path.join(REPO, t.get('html', 'bounds-comparison.html'))
    compare.main(runs + ['--format', 'html', '--header', os.path.join(REPO, t['header']), '-o', out])
    print('table ->', os.path.relpath(out, REPO))
    if not webbrowser.open('file://' + out):
        print('open it in a browser: file://' + out)

def check(args):
    man = json.load(open(MANIFEST))
    base = args[0] if args else man[-1]['name']
    old = compare.load_run(base)
    new = {e['id']: e for e in extract.snapshot()}
    bad = []
    for i, e in new.items():
        o = old.get(i)
        if o is None: print('new bound', i); continue
        d = compare.direction(o, e)
        if d == '':
            bad.append(i); print('other shape', i, '\n   ', o['template'], '\n   ', e['template'])
        elif d in ('↑', '↕'):
            bad.append(i); print('higher', i, o['constants'], '->', e['constants'])
    for i in old:
        if i not in new: print('removed bound', i)
    print(f'{len(bad)} bound(s) higher or of another shape than in {base}')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[1] not in ('snapshot', 'minimise', 'table', 'show', 'check'):
        raise SystemExit(__doc__)
    {'snapshot': snapshot, 'minimise': minimise, 'table': table, 'show': show, 'check': check}[sys.argv[1]](sys.argv[2:])
