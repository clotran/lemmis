# Lemmis

PLAN.md is the design and the milestone order. The proofs live in
`model/`, certified by ACL2 (`/Users/james/clotran/acl2/saved_acl2`).

## Proof work: keep the context small

Every turn re-reads the whole context, so a long run with a big context
costs turns x context. Past Lemmis runs reached 1,600 turns at ~480k
context (~776M tokens), mostly from ACL2 output, greps, and whole-file
reads left sitting in the context.

- **Certify only via make:** `make model`, or `make model/<book>.cert`
  for one book. ACL2's output goes to `build/<book>.log`; make prints one
  line per book, plus at most 20 error lines. Never run `saved_acl2` with
  its output coming back to you.
- **Read a failed proof's checkpoints only:**
  `grep -n -A30 'Key checkpoint' build/<book>.log | head -80`. Never cat
  a log.
- **Time limits:** each book is killed at `CERT_SECS` seconds of CPU
  (default 1800; `ulimit -t`, so a loaded machine doesn't trip it). A proof that needs longer is wrong:
  disable what's opening, add the lemma, give the hint. Don't raise the limit.
- **Big definitions are disabled by default.** An interpreter, a parser
  step, or any definition with many cases is disabled right after it's
  defined, and opened only through small lemmas, one per case. A theorem
  enables exactly what it needs. Adding a case then touches its own lemma
  instead of blowing up every proof above it.
- **Keep books small:** under ~800 lines. Split a book before it grows past
  that, so a change re-certifies only its own part.
- **Read files by section** (`sed -n A,Bp`, `grep -n`), and don't re-read
  what's already in the context. No images unless the task is visual.
- **Rethink after 3 failed attempts at one lemma.**
- **Don't end your turn while make or ACL2 is running.** Wait in the
  foreground. Kill whatever you started before you finish.
- **Hand off:** at ~300k tokens, commit what's green as WIP, write down
  exactly what remains, and stop. A fresh agent resumes from the WIP; that
  costs far less than one run dragging on.

## Gates

`make model` (every book certifies), then `make check` (fsem against
gfortran and flang). Both must pass before a commit.
