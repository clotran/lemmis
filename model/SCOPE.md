# Stage A's Scope: the grammar, and how much of it is proved

PLAN.md's Scope is the Fortran scientists write: free form, modules,
procedures, arrays, the loops, `pure` and `elemental`, the intrinsics
most used. This file lists the syntax rules of J3/24-007 (the Fortran
2023 working draft, read for this list) that the Scope needs, and for
each one whether the model has it. A rule counts as **proved** when
its grammar is in a book (fgram.lisp for expressions, fstmt.lisp for
statements, fprog.lisp for program units) and that book's parser is
proved to accept exactly that grammar (`fp-`, `fps-`, `fpu-sound` and
`-complete`), for every alternative the Scope uses; **part** when only
some alternatives are in; **no** otherwise.

Score: **113 of 138** Scope rules proved (82%); 21 more in part; 4 not yet in.

## The books

- `fgram.lisp`: the expression grammar as `fg` (a recognizer of parse
  trees) and `fy` (the tokens a tree spells), over flex's tokens.
- `fparse.lisp`: `fp`, recursive descent with one token of lookahead
  (two for a keyword argument), and
  - `fp-sound`: what fp answers is a tree of the grammar, and spells the
    tokens it read;
  - `fp-complete`: on the spelling of any tree, followed by any token
    that does not continue it, fp answers that tree -- so the grammar is
    unambiguous and fp accepts every sentence of it;
  - `fp-cost`: a successful parse makes at most 32 calls per token it
    reads, plus a constant per nonterminal (`fp-d`, at most 17) -- with
    fp-complete, n tokens are read in at most 32n + 17 calls.
  All certify in about 25 s.
- `fstmt.lisp`: one statement's tokens, the same way: `fgs`, `fys`, the
  parser `fps` (its kind known from the first tokens), `fps-sound`,
  `fps-complete` (followed by nothing: a statement is whole) and
  `fps-cost`: at most 64 calls per token read, fp's among them, plus
  `fps-d` (at most 48). About 8 minutes.
- `fprog.lisp`: program units over statement trees: `fgu`, `fyu`, the
  parser `fpu`, `fpu-sound` (on statement trees), `fpu-complete` and
  `fpu-cost`: at most 32 calls per statement, plus `fpu-d` (at most 12).
  About 5 minutes.
- `fmean.lisp`: the meaning (item 2). `fortran-parse` is flex, then fps
  on each statement, then fpu; `fortran-parse-sound`: what it accepts is
  a program of the grammar.
- `freal.lisp`: the binary32 and binary64 formats of ISO/IEC 60559 for
  real kinds 4 and 8: rounding to nearest even, signed zeros, infinities,
  NaN, subnormals, a correctly rounded SQRT; `assert-event` tests against
  values clj computes, and the cost of its integer square root.
- `flex.lisp`: free source form (6.3.2) to statements of tokens, with
  `assert-event` tests. Not proved; it is checked by running programs.

## Subset restrictions (each keeps a program's meaning; a program outside them is outside the subset)

- A name is never one of the words a statement can begin with
  (`*fkeywords*`: `if`, `do`, `end`, `integer`, ...). Fortran has no
  reserved words; with this, each statement's kind is known from its
  first tokens.
- No character expressions: R1011's concat-op and character variables
  are out; a character literal may appear (as a PRINT item).
- No defined operators (R1003, R1023 have no defined-unary-op or
  defined-binary-op), no conditional expressions (R1002), no derived
  types, no labels, no construct names, no `(/ ... /)` constructors.
- `::` is lexed as two `:` tokens (it is two colons in a triplet
  `a(::2)` too); a token is not split across lines, and a character
  context is not continued (6.3.2.4p3, p4).

## The rules

| Rule | Name | Status | Note |
|---|---|---|---|
| R501 | program | proved |  |
| R502 | program-unit | proved | main-program, external-subprogram, module |
| R503 | external-subprogram | proved |  |
| R504 | specification-part | proved | use-stmts, IMPLICIT NONE, type-declaration-stmts |
| R505 | implicit-part | proved | IMPLICIT NONE only |
| R507 | declaration-construct | part | type-declaration-stmt only; no derived-type-def, interface-block |
| R509 | execution-part | proved |  |
| R511 | internal-subprogram-part | proved |  |
| R512 | internal-subprogram | proved |  |
| R514 | executable-construct | part | action-stmt, do-construct, if-construct, case-construct; no block-construct |
| R515 | action-stmt | part | assignment, call, cycle, exit, continue, if-stmt, print, return, stop; no allocate, deallocate |
| R516 | keyword | proved | as an actual-arg-spec's keyword |
| R601 | alphanumeric-character | proved | in R603 |
| R603 | name | proved | lower case (flex); not a statement keyword |
| R604 | constant | part | literal-constant; named-constant as a designator |
| R605 | literal-constant | part | int, real, logical, char; no complex, boz |
| R708 | int-literal-constant | proved | |
| R709 | kind-param | proved | |
| R711 | digit-string | proved | |
| R714 | real-literal-constant | proved | the significand's two forms, E and D, a kind (C721) |
| R715 | significand | proved |  |
| R716 | exponent-letter | proved |  |
| R717 | exponent | proved |  |
| R724 | char-literal-constant | part | no kind-param prefix |
| R725 | logical-literal-constant | proved | |
| R703 | declaration-type-spec | proved | intrinsic-type-spec |
| R704 | intrinsic-type-spec | part | INTEGER, REAL, LOGICAL; no COMPLEX, CHARACTER, DOUBLE PRECISION |
| R705 | integer-type-spec | proved |  |
| R706 | kind-selector | proved |  |
| R777 | array-constructor | part | lbracket ac-spec rbracket |
| R778 | ac-spec | part | ac-value-list |
| R779 | lbracket | proved | |
| R780 | rbracket | proved | |
| R781 | ac-value | part | expr; no ac-implied-do |
| R801 | type-declaration-stmt | proved |  |
| R802 | attr-spec | part | DIMENSION, INTENT, PARAMETER, VALUE; no ALLOCATABLE, SAVE |
| R803 | entity-decl | proved |  |
| R804 | object-name | proved |  |
| R805 | initialization | proved | = constant-expr |
| R814 | array-spec | part | explicit-shape-spec-list, assumed-shape-spec-list; no deferred-shape |
| R815 | explicit-shape-spec | proved |  |
| R816 | lower-bound | proved |  |
| R817 | upper-bound | proved |  |
| R820 | assumed-shape-spec | proved |  |
| R828 | intent-spec | proved | IN, OUT, INOUT, IN OUT |
| R866 | implicit-stmt | proved | IMPLICIT NONE |
| R901 | designator | proved | object-name, array-element, array-section |
| R902 | variable | proved | in assignment-stmt |
| R911 | data-ref | proved | one part-ref (no derived types) |
| R912 | part-ref | proved | |
| R917 | array-element | proved | |
| R918 | array-section | proved | |
| R919 | subscript | proved | |
| R921 | section-subscript | part | subscript, subscript-triplet; no vector-subscript |
| R922 | subscript-triplet | proved | |
| R924 | stride | proved | |
| R1001 | primary | part | literal, designator, array-constructor, function-reference, ( expr ) |
| R1003 | level-1-expr | proved | no defined-unary-op |
| R1005 | mult-operand | proved | |
| R1006 | add-operand | proved | |
| R1007 | level-2-expr | proved | |
| R1008 | power-op | proved | |
| R1009 | mult-op | proved | |
| R1010 | add-op | proved | |
| R1011 | level-3-expr | no | concat-op: no character expressions yet |
| R1012 | concat-op | no | |
| R1013 | level-4-expr | proved | |
| R1014 | rel-op | proved | |
| R1015 | and-operand | proved | |
| R1016 | or-operand | proved | |
| R1017 | equiv-operand | proved | |
| R1018 | level-5-expr | proved | |
| R1019 | not-op | proved | |
| R1020 | and-op | proved | |
| R1021 | or-op | proved | |
| R1022 | equiv-op | proved | |
| R1023 | expr | proved | no defined-binary-op |
| R1033 | assignment-stmt | proved |  |
| R1101 | block | proved |  |
| R1119 | do-construct | proved |  |
| R1120 | do-stmt | proved | nonlabel-do-stmt |
| R1122 | nonlabel-do-stmt | proved |  |
| R1123 | loop-control | part | do-variable = e, e [, e]; WHILE; no CONCURRENT |
| R1124 | do-variable | proved |  |
| R1125 | concurrent-header | no | |
| R1126 | concurrent-control | no | |
| R1133 | end-do | proved | end-do-stmt |
| R1134 | end-do-stmt | proved |  |
| R1135 | cycle-stmt | proved |  |
| R1136 | if-construct | proved |  |
| R1137 | if-then-stmt | proved |  |
| R1138 | else-if-stmt | proved |  |
| R1139 | else-stmt | proved |  |
| R1140 | end-if-stmt | proved |  |
| R1141 | if-stmt | proved |  |
| R1142 | case-construct | proved | at most one DEFAULT (C1151) |
| R1143 | select-case-stmt | proved | no construct name |
| R1144 | case-stmt | proved |  |
| R1145 | end-select-stmt | proved |  |
| R1146 | case-expr | proved |  |
| R1147 | case-selector | proved | ( case-value-range-list ), DEFAULT |
| R1148 | case-value-range | proved | all four forms |
| R1149 | case-value | proved |  |
| R1158 | exit-stmt | proved |  |
| R1161 | continue-stmt | proved |  |
| R1162 | stop-stmt | part | no stop-code |
| R1212 | print-stmt | proved |  |
| R1215 | format | part | * only |
| R1217 | output-item | part | expr; no io-implied-do |
| R1401 | main-program | proved | the program-stmt required |
| R1402 | program-stmt | proved |  |
| R1403 | end-program-stmt | proved |  |
| R1404 | module | proved |  |
| R1405 | module-stmt | proved |  |
| R1406 | end-module-stmt | proved |  |
| R1407 | module-subprogram-part | proved |  |
| R1408 | module-subprogram | proved |  |
| R1409 | use-stmt | part | no rename-list |
| R1410 | module-nature | proved |  |
| R1412 | only | part | only-use-name; no rename |
| R1520 | function-reference | proved | |
| R1521 | call-stmt | proved |  |
| R1522 | procedure-designator | proved | procedure-name |
| R1523 | actual-arg-spec | proved | |
| R1524 | actual-arg | part | expr (a variable is an expr's designator) |
| R1529 | prefix | proved |  |
| R1530 | prefix-spec | proved | type-spec, ELEMENTAL, IMPURE, NON_RECURSIVE, PURE, RECURSIVE |
| R1532 | function-subprogram | proved |  |
| R1533 | function-stmt | proved |  |
| R1534 | dummy-arg-name | proved |  |
| R1535 | suffix | proved | RESULT ( name ) |
| R1536 | end-function-stmt | proved |  |
| R1537 | subroutine-subprogram | proved |  |
| R1538 | subroutine-stmt | proved |  |
| R1539 | dummy-arg | proved | dummy-arg-name |
| R1540 | end-subroutine-stmt | proved |  |
| R1545 | return-stmt | proved | no alternate return |
| R1546 | contains-stmt | proved |  |
