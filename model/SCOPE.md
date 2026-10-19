# Stage A's Scope: the grammar, and how much of it is proved

PLAN.md's Scope is the Fortran scientists write: free form, modules,
procedures, arrays, the loops, `pure` and `elemental`, the intrinsics
most used. This file lists the syntax rules of J3/24-007 (the Fortran
2023 working draft, read for this list) that the Scope needs, and for
each one whether the model has it. A rule counts as **proved** when
fgram.lisp has it as grammar and fparse.lisp's parser is proved to
accept exactly that grammar (`fp-sound`, `fp-complete`), for every
alternative the Scope uses; **part** when only some alternatives are in;
**next** when its statement or construct grammar is written but not yet
proved (fstmt.lisp, fprog.lisp, not yet in the books); **no** otherwise.

Score: **38 of 139** Scope rules proved; 9 more in part; 75 written (statements, units) and next to prove; 16 not yet in.

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
| R501 | program | next | |
| R502 | program-unit | next | main-program, external-subprogram, module |
| R503 | external-subprogram | next | |
| R504 | specification-part | next | use-stmts, IMPLICIT NONE, type-declaration-stmts |
| R505 | implicit-part | next | IMPLICIT NONE only |
| R507 | declaration-construct | next | type-declaration-stmt only |
| R509 | execution-part | next | |
| R511 | internal-subprogram-part | next | |
| R512 | internal-subprogram | next | |
| R514 | executable-construct | next | action-stmt, do-construct, if-construct |
| R515 | action-stmt | next | assignment, call, cycle, exit, continue, if-stmt, print, return, stop |
| R516 | keyword | proved | as an actual-arg-spec's keyword |
| R601 | alphanumeric-character | proved | in R603 |
| R603 | name | proved | lower case (flex); not a statement keyword |
| R604 | constant | part | literal-constant; named-constant as a designator |
| R605 | literal-constant | part | int, logical, char; no real, complex, boz |
| R708 | int-literal-constant | proved | |
| R709 | kind-param | proved | |
| R711 | digit-string | proved | |
| R714 | real-literal-constant | no | reals are next after the statements |
| R715 | significand | no | |
| R716 | exponent-letter | no | |
| R717 | exponent | no | |
| R724 | char-literal-constant | part | no kind-param prefix |
| R725 | logical-literal-constant | proved | |
| R703 | declaration-type-spec | next | intrinsic-type-spec |
| R704 | intrinsic-type-spec | next | INTEGER, LOGICAL |
| R705 | integer-type-spec | next | |
| R706 | kind-selector | next | |
| R777 | array-constructor | part | lbracket ac-spec rbracket |
| R778 | ac-spec | part | ac-value-list |
| R779 | lbracket | proved | |
| R780 | rbracket | proved | |
| R781 | ac-value | part | expr; no ac-implied-do |
| R801 | type-declaration-stmt | next | |
| R802 | attr-spec | next | DIMENSION, INTENT, PARAMETER, VALUE |
| R803 | entity-decl | next | |
| R804 | object-name | next | |
| R805 | initialization | next | = constant-expr |
| R814 | array-spec | next | explicit-shape-spec-list, assumed-shape-spec-list |
| R815 | explicit-shape-spec | next | |
| R816 | lower-bound | next | |
| R817 | upper-bound | next | |
| R820 | assumed-shape-spec | next | |
| R828 | intent-spec | next | IN, OUT, INOUT, IN OUT |
| R866 | implicit-stmt | next | IMPLICIT NONE |
| R901 | designator | proved | object-name, array-element, array-section |
| R902 | variable | next | in assignment-stmt |
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
| R1033 | assignment-stmt | next | |
| R1101 | block | next | |
| R1119 | do-construct | next | |
| R1120 | do-stmt | next | nonlabel-do-stmt |
| R1122 | nonlabel-do-stmt | next | |
| R1123 | loop-control | next | do-variable = e, e [, e]; WHILE; no CONCURRENT |
| R1124 | do-variable | next | |
| R1125 | concurrent-header | no | |
| R1126 | concurrent-control | no | |
| R1133 | end-do | next | end-do-stmt |
| R1134 | end-do-stmt | next | |
| R1135 | cycle-stmt | next | |
| R1136 | if-construct | next | |
| R1137 | if-then-stmt | next | |
| R1138 | else-if-stmt | next | |
| R1139 | else-stmt | next | |
| R1140 | end-if-stmt | next | |
| R1141 | if-stmt | next | |
| R1142 | case-construct | no | |
| R1143 | select-case-stmt | no | |
| R1144 | case-stmt | no | |
| R1145 | end-select-stmt | no | |
| R1146 | case-expr | no | |
| R1147 | case-selector | no | |
| R1148 | case-value-range | no | |
| R1149 | case-value | no | |
| R1158 | exit-stmt | next | |
| R1161 | continue-stmt | next | |
| R1162 | stop-stmt | next | no stop-code |
| R1212 | print-stmt | next | |
| R1215 | format | next | * |
| R1217 | output-item | next | expr |
| R1401 | main-program | next | the program-stmt required |
| R1402 | program-stmt | next | |
| R1403 | end-program-stmt | next | |
| R1404 | module | next | |
| R1405 | module-stmt | next | |
| R1406 | end-module-stmt | next | |
| R1407 | module-subprogram-part | next | |
| R1408 | module-subprogram | next | |
| R1409 | use-stmt | next | |
| R1410 | module-nature | next | |
| R1412 | only | next | only-use-name |
| R1520 | function-reference | proved | |
| R1521 | call-stmt | next | |
| R1522 | procedure-designator | proved | procedure-name |
| R1523 | actual-arg-spec | proved | |
| R1524 | actual-arg | part | expr (a variable is an expr's designator) |
| R1529 | prefix | next | |
| R1530 | prefix-spec | next | type-spec, ELEMENTAL, IMPURE, NON_RECURSIVE, PURE, RECURSIVE |
| R1532 | function-subprogram | next | |
| R1533 | function-stmt | next | |
| R1534 | dummy-arg-name | next | |
| R1535 | suffix | next | RESULT ( name ) |
| R1536 | end-function-stmt | next | |
| R1537 | subroutine-subprogram | next | |
| R1538 | subroutine-stmt | next | |
| R1539 | dummy-arg | next | dummy-arg-name |
| R1540 | end-subroutine-stmt | next | |
| R1545 | return-stmt | next | no alternate return |
| R1546 | contains-stmt | next | |
