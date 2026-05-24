import sys, io, json, time, os
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

d = json.load(sys.stdin)
branch = os.environ.get('GIT_BRANCH', '')

# ANSI helpers
def c(code): return f'\033[{code}m'
R    = c(0)    # reset
BOLD = c(1)
DIM  = c(2)
GRAY = c(90)   # dark gray
CYAN = c(96)   # bright cyan  — model name
YEL  = c(93)   # bright yellow — directory
MAG  = c(95)   # bright magenta — git branch
GRN  = c(32)   # green
ORG  = c(33)   # yellow/orange
RED  = c(31)   # red

def bar_color(pct):
    if pct < 60: return GRN
    if pct < 80: return ORG
    return RED

def bar(pct, width=8):
    pct = max(0, min(100, int(pct)))
    filled = round(pct * width / 100)
    bc = bar_color(pct)
    b = f'{bc}{"▓" * filled}{R}{GRAY}{"░" * (width - filled)}{R}'
    if pct >= 85:
        b += f' {RED}⚠{R}'
    return b

def pct_str(pct):
    return f'{bar_color(pct)}{int(pct)}%{R}'

def fmt_reset(ts):
    if not ts: return ''
    diff = int(ts) - int(time.time())
    if diff <= 0: return ''
    h, rem = divmod(diff, 3600)
    return f'{h}h{rem//60:02d}m' if h else f'{rem//60}m'

def shorten_path(p):
    if not p: return ''
    p = p.replace('\\', '/')
    home = os.path.expanduser('~').replace('\\', '/')
    if p.startswith(home):
        p = '~' + p[len(home):]
    parts = p.rstrip('/').split('/')
    if len(parts) > 2:
        return '…/' + '/'.join(parts[-2:])  # …/parent/dir
    return '/'.join(parts)

model   = ((d.get('model') or {}).get('display_name') or '?').replace('Claude ', '')
ctx_pct = (d.get('context_window') or {}).get('used_percentage')
rl      = d.get('rate_limits') or {}
fh      = rl.get('five_hour') or {}
sd      = rl.get('seven_day') or {}
cwd     = (d.get('workspace') or {}).get('current_dir', '')

SEP   = f'  {GRAY}│{R}  '        # dim │
parts = [f'{BOLD}{CYAN}◆ {model}{R}']  # ◆ model

if cwd:
    parts.append(f'{YEL}⌂ {shorten_path(cwd)}{R}')  # ⌂ dir

if ctx_pct is not None:
    parts.append(f'{DIM}ctx{R} {bar(ctx_pct)} {pct_str(ctx_pct)}')

fh_pct = fh.get('used_percentage')
if fh_pct is not None:
    s = f'{DIM}⏱ 5h{R} {bar(fh_pct)} {pct_str(fh_pct)}'  # ⏱
    r = fmt_reset(fh.get('resets_at'))
    if r: s += f' {GRAY}↺{r}{R}'  # ↺
    parts.append(s)

sd_pct = sd.get('used_percentage')
if sd_pct is not None:
    s = f'{DIM}7d{R} {bar(sd_pct)} {pct_str(sd_pct)}'
    r = fmt_reset(sd.get('resets_at'))
    if r: s += f' {GRAY}↺{r}{R}'
    parts.append(s)

if branch:
    parts.append(f'{MAG}⎇  {branch}{R}')  # ⎇

print(SEP.join(parts), end='')
