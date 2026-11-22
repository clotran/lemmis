# Lemmis version 0: the grammar the reader accepts

Rule numbers are J3/24-007's (the Fortran 2023 draft), as model/SCOPE.md cites them; model/
(the proved parser) is the reference for what Fortran accepts. Version 0 accepts a SUBSET of
each rule: the alternatives listed. Anything else is refused with path:line:column and the
reason (the numbered list is in README.md). Extensions are marked **ext**: each is text
Fortran rejects (PLAN.md "The rule"), so no valid Fortran changes meaning.

## Source form (6.3.2, free form)
- Case-insensitive names and keywords; a name is folded to lower case (R603).
- `!` starts a comment (6.3.2.3); `;` separates statements (6.3.2.5); `&` at the end of a
  line continues it, and a leading `&` on the next line is skipped (6.3.2.4).
- No statement labels (R611): refused.
- **ext** `?` is a name character (`empty?`); `\`...\`` is a Clojure name spelled
  exactly (`\`clojure.string/join\``), case kept.

## Program units
- R1404 module: `module` name, specification part, [`contains` module-subprogram ...],
  `end` [`module` [name]]. **ext**: a dotted name `module my.solver` (R603 rejects `.`).
- R1401 main-program: `program` name ... [`contains` ...] `end` [`program` [name]]; its
  internal procedures may not use the host's variables (host association: refused).
- R1409 use-stmt: `use` name [`,` `only:` [only-list]] or `use` name `,` rename-list;
  R1412 only: a name or `local => use-name`. **ext**: a dotted name (`use clojure.string`).
  `use iso_fortran_env` gives its kind constants (int8..int64, real32, real64) at read time.
- R866 implicit-stmt: only `implicit none`, and it is required.
- R1532/R1533 function: [prefix] `function` name `(` [dummy-args] `)` [`result(` name `)`];
  R1530 prefix-spec: `pure`, `elemental` (no meaning change on these programs),
  `recursive`, and a type-spec. R1536 `end` [`function` [name]].
- R1537/R1538 subroutine: [prefix] `subroutine` name [`(` [dummy-args] `)`] ...
  R1540 `end` [`subroutine` [name]].
- R1546 contains; R807-ish access statements `private`, `public` [`::` names].

## Declarations
- R801 type-declaration-stmt: type-spec [`,` attr-spec ...] [`::`] entity-decl-list.
- R704 intrinsic-type-spec: `integer`[kind], `real`[kind], `double precision`,
  `complex`[kind], `logical`, `character`[char-selector].
  R706 kind-selector: `(` [`kind=`] k `)` where k is a literal or a named constant known
  at read time (a parameter, `kind(...)` of a literal, an iso_fortran_env name).
  Kinds: integer 1 2 4 8, real 4 8, complex 4 8.
  R721 char-selector: `(` [`len=`] n | `*` `)`, `(len=`...`)`, `*n`.
- R802 attr-spec: `parameter`, `intent(in|out|inout)` (R828), `dimension(` array-spec `)`.
- **ext** `val ::` name-list: dummy arguments that are Clojure values (any value, immutable).
- R803 entity-decl: name [`(` array-spec `)`] [`=` expr] (initialization only with
  `parameter`, which is a constant).
- R814 array-spec, rank 1: R815 explicit-shape `[lower:]upper`, R820 assumed-shape `:`
  or `lower:`, and `*` for a dummy.

## Executable statements (R514, R515)
- R1033 assignment: variable `=` expr; the variable a scalar name or an array element
  `a(i)` (R917). **ext**: `val` name `=` expr (an immutable binding, a Clojure value).
- R1136-R1140 if construct (`if (` e `) then`, `else if (` e `) then`, `else`, `end if`);
  R1141 if-stmt `if (` e `)` action-stmt.
- R1119-R1134 do construct, non-labelled: `do`, `do` var `=` e1, e2 [, e3],
  `do while (` e `)`; `end do`. No construct names.
- R1158 exit, R1135 cycle (innermost loop), R1545 return, R1161 continue.
- R1521 call-stmt: `call` name [`(` actual-args `)`].
- R1212 print-stmt: `print *` [`,` output-item-list]; R1211 `write(*,*)` the same.

## Expressions (R1001-R1023)
Fortran's precedence, high to low: `**` (right to left), `* /`, unary and binary `+ -`,
`//`, the relations (`== /= < <= > >=` and `.eq.` ... `.ge.`), `.not.`, `.and.`, `.or.`,
`.eqv. .neqv.`. R1001 primary: a literal (R708 integer with `_kind`, R714 real with
`e`/`d` exponent and `_kind`, R718 complex `(re, im)`, R724 character `'..'` or `".."`,
R725 `.true.`/`.false.`), a name, an array element, a function reference (R1520) with
actual args (R1523, `kind=` for intrinsics), `(` expr `)`.
**ext** primaries:
- `->> e stage ...` and `-> e stage ...`: a pipeline; each stage is a name or a call without
  its threaded argument, the stages written one after another to the end of the expression.
- `#[a, b, c]` a persistent vector, `#{k v, k v}` a persistent map, `:name` a keyword.
- any undeclared name is a Clojure name: `f(args)` calls it, `f` alone is its value.
