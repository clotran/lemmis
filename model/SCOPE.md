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

Score: **161 of 199** Scope rules proved (81%); 38 more in part; none not yet in.

## Theorem 3: checked against the compilers (status)

Not a theorem: a test, run by `make check` (exit 1 on any difference).

- **Oracle programs**: check-fsem.bb's 7 fsyn cases (the subset clotran's
  generator emits) and the 37 whole programs of `cases/`, each run by the
  model and by gfortran (-std=f2018) and flang; all agree, and the two
  compilers agree with each other on all of them but `modzero.f90`, whose
  values the standard leaves open (below). One, `acdotyped.f90`,
  runs under flang only: gfortran 16 rejects R783's integer-type-spec
  (a case's first line `! not gfortran: why` says so).
- **The fuzzer**: `fuzz.bb` (`make fuzz`, run by `make check` with seed
  1, 40 programs, about 35 s; `make fuzz FUZZ_SEED=7 FUZZ_N=100` for more).
  Each program is a module (a derived type; an integer and a real(8)
  function; a subroutine with INTENT IN, INOUT and OUT) and a main program
  with an internal subroutine (host association); integer, real(8),
  real(4), logical, character(6) and structure-component scalars and one
  integer array; assignment (to a substring too), DO (a step, EXIT,
  CYCLE), DO WHILE, IF constructs, SELECT CASE (ranges, lists, DEFAULT),
  CALL, PRINT * (a whole structure too); + - * /, //, MOD, MODULO, MIN,
  MAX, ABS, SIGN, SQRT, REAL/DBLE, INT, NINT, FLOOR, LEN_TRIM, TRIM,
  substrings, structure constructors, the relations and the logical
  operators. A real is compared by its value, as check-fsem does
  (`fmatch.clj`). Not generated: allocatables, array sections and
  constructors, complex, I/O under a format, recursion -- checked by the
  oracle programs only. A program whose run turns on a processor-dependent
  value (the model stops with :pd) is counted, not compared; a
  disagreement is kept in `build/fuzz/` as a regression case. Seeds 1-5
  (40 to 120 programs each): all agree. It found DIM missing (not in the
  Scope); a whole structure printed as `?` (now its components, 12.6.3p7:
  `cases/dtprint.f90`); and the sign of a real MOD or MODULO's zero
  result, which the standard leaves open (16.9.145, 16.9.146 give the
  value; gfortran answers A's sign for MOD and P's for MODULO, flang
  another for MOD): the model's value is processor dependent there
  (`cases/modzero.f90`).
- **FCVS**: scored, not failed, and only when `fcvs/` is fetched
  (`bb fetch-fcvs.bb`; not committed): 63 of 180 programs print their
  reference output exactly (FM002-010, 012, 016-021, 026, 030-045,
  060, 061, 097, 098, 109, 201-205, 251, 254, 256, 301, 306, 352-355,
  359-362, 368, 718, 801, 805-807, 812). Of the rest, 75 stop at a statement outside the
  subset (first: fixed form's blank-free COMPLEX 16, COMMON 14, OPEN 11,
  ...); 37 at a processor-dependent value (most an
  approximated SIN, EXP, LOG, ATAN2, ... the program compares within a
  tolerance); 5 at an I/O end or unit. (The score read 0 until the
  harness dropped the "exit 0" line LLVM's reference outputs end with.)
- **flang's parse tree** (PLAN.md's parsing oracle) is not compared yet.

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
  - `fp-cost` (`fparse-cost.lisp`): a successful parse makes at most 32 calls per token it
    reads, plus a constant per nonterminal (`fp-d`, at most 19) -- with
    fp-complete, n tokens are read in at most 32n + 17 calls.
  All certify in about a minute.
- `fstmt-gram.lisp` and `fstmt.lisp`: one statement's tokens, the same way:
  `fgs`, `fys` (fstmt-gram), the parser `fps` (fstmt) (its kind known from the first tokens); `fstmt-sound.lisp`:
  `fps-sound`; `fstmt-complete.lisp`: `fps-complete` (followed by nothing:
  a statement is whole);
  `fstmt-cost.lisp`: `fps-cost`: at most 64 calls per token read, fp's among them, plus
  `fps-d` (at most 48), over `fps-steps` (generated, its case clauses split between `fstmt-steps.lisp` and `fstmt-steps2.lisp`); the
  I/O control list's nonterminals and READ and WRITE are bounded first, on
  their own. The tokens and predicates the grammar uses (labels, formats,
  the control list's constraints) are `fstmt-base.lisp`'s. About 8 minutes.
- `fprog.lisp`: program units over statement trees: `fgu`, `fyu`, the
  parser `fpu`, `fpu-sound` (on statement trees), `fpu-complete` and
  `fpu-cost` (`fprog-cost.lisp`): at most 32 calls per statement, plus `fpu-d` (at most 12).
  About 5 minutes.
- `fval.lisp`, `fhelp.lisp`, `fio.lisp`, `fmean.lisp`, `frun.lisp`: the meaning (item 2): the
  values, state and intrinsics; the helpers and labels; formatted and
  list-directed I/O on the unit * (13); the evaluation itself; a whole
  program from its text (`fmean-cost.lisp`: its data operations' cost, and tests). `fortran-parse` is flex, then fps
  on each statement, then fpu; `fortran-parse-sound`: what it accepts is
  a program of the grammar.
- `fspec.lisp`: FORTRAN 77's specific intrinsic names (16.8, Tables 16.2,
  16.3: IABS, AMOD, IFIX, FLOAT, SNGL, IDINT, DSQRT, AMAX0, MAX1, ...), each
  its generic on arguments of the one type and kind its row gives (others
  an error), DPROD, ICHAR and IACHAR (ASCII codes); DIM, AINT, ANINT, ATAN2 are fval's
  (`cases/specific.f90`). A specific name as an actual argument is not in
  the subset.
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
- Character is of the default kind only (no KIND= in R721, no kind-param
  on a literal), and scalar or an array element by element. A substring's
  parent is a variable or a named constant (not a literal), and a READ's
  input item is not a substring. A character variable defined only in part
  (by substrings) holds the code 0 at its undefined characters, so a
  program of the subset writes no such character. After `CHARACTER*n,`
  (R722's comma) the first entity is not named `parameter`, `value`,
  `intent`, `dimension`, `save` or `allocatable`.
- No defined operators (R1003, R1023 have no defined-unary-op or
  defined-binary-op), no conditional expressions (R1002), no labels, no
  construct names, no `(/ ... /)` constructors.
- An array constructor's ac-value that begins with `(` is an
  ac-implied-do (write `+(a + b)` or `1 * (a + b)` for a parenthesized
  first primary), so each ac-value's kind is known from its first token;
  a constructor has at least one value (its type is its first value's,
  no type-spec).
- A BLOCK's declarations are type declarations, none SAVE'd or
  initialized but a named constant: nothing a BLOCK keeps from one
  execution to the next. `block` is among `*fkeywords*`.
- R-numbers are J3/24-007's, checked against the draft's text (each
  row's number names its rule there).
- Derived types: a part-ref of an array of structures followed by
  another part-ref is an element (no `a(1:2)%x`); a dummy argument's
  type is its actual's by the type's name; no type-bound procedures or
  parameters; a structure is read by its components (printed whole, by its components in order: 12.6.3p7), and a
  component is not an actual argument that the procedure defines.
- Complex: a part of a complex literal is a signed literal, not a named
  constant; a complex is printed by list-directed output only (not
  read, nor under a format), and is not an argument of the reductions
  (SUM, MAXVAL, ...). Complex * / ** and ABS are processor
  approximations (10.1.5.2.4): the model answers a value only where
  every step of the textbook formula (and, for /, Smith's) is exact,
  else a processor-dependent value; a zero part's sign is the textbook
  formula's.
- ALLOCATABLE: an array of deferred shape, not a dummy argument, a
  component, a scalar, SAVE'd or initialized. Intrinsic assignment to it
  does not allocate or reallocate (10.2.1.3): the variable is allocated
  first, with the expression's shape, else the run stops with an error.
  `allocate` and `deallocate` are among `*fkeywords*`.
- A section with a vector subscript (R925) is defined only when no index repeats (9.5.3.4.3p3: the model
  would keep the last value), and is not an actual argument the procedure defines (it is not definable).
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
| R505 | implicit-part | proved | IMPLICIT NONE first; IMPLICIT statements among the declaration-constructs (R507) |
| R507 | declaration-construct | part | type-declaration-stmt, derived-type-def, save-stmt, dimension-stmt, implicit-stmt; no interface-block |
| R509 | execution-part | proved |  |
| R511 | internal-subprogram-part | proved |  |
| R512 | internal-subprogram | proved |  |
| R514 | executable-construct | part | action-stmt, block-construct, do-construct, if-construct, case-construct |
| R515 | action-stmt | proved | allocate, assignment, call, cycle, deallocate, exit, continue, if-stmt, print, return, stop |
| R516 | keyword | proved | as an actual-arg-spec's keyword |
| R601 | alphanumeric-character | proved | in R603 |
| R603 | name | proved | lower case (flex); not a statement keyword |
| R611 | label | proved | one to five digits, not all zero (C613) |
| R604 | constant | part | literal-constant; named-constant as a designator |
| R605 | literal-constant | part | int, real, complex, logical, char; no boz |
| R708 | int-literal-constant | proved | |
| R709 | kind-param | proved | |
| R711 | digit-string | proved | |
| R714 | real-literal-constant | proved | the significand's two forms, E and D, a kind (C721) |
| R715 | significand | proved |  |
| R716 | exponent-letter | proved |  |
| R717 | exponent | proved |  |
| R718 | complex-literal-constant | proved | ( real-part , imag-part ), told from ( expr ) by its "," |
| R719 | real-part | part | signed-int-literal-constant, signed-real-literal-constant (an :expr tree, cpart-p); no named-constant |
| R720 | imag-part | part | as R719 |
| R724 | char-literal-constant | part | no kind-param prefix |
| R725 | logical-literal-constant | proved | |
| R701 | type-param-value | part | scalar-int-expr, `*` (a dummy's or a named constant's length); no `:` |
| R703 | declaration-type-spec | proved | intrinsic-type-spec, TYPE ( derived-type-spec ) |
| R704 | intrinsic-type-spec | proved | INTEGER, REAL, DOUBLE PRECISION (`doubleprecision` split by flex), COMPLEX, CHARACTER, LOGICAL |
| R705 | integer-type-spec | proved |  |
| R706 | kind-selector | proved |  |
| R721 | char-selector | part | length-selector; no KIND= |
| R722 | length-selector | proved | ( [LEN =] type-param-value ), * char-length [,] (C724, C725) |
| R723 | char-length | proved | ( type-param-value ), int-literal-constant |
| R726 | derived-type-def | proved | derived-type-stmt [component-part] end-type-stmt (no type-param-def-stmt, private-or-sequence, type-bound-procedure-part) |
| R727 | derived-type-stmt | part | TYPE [::] type-name; no type-attr-spec-list, type-param-name-list |
| R730 | end-type-stmt | proved | END TYPE [type-name] (C751) |
| R735 | component-part | proved | |
| R736 | component-def-stmt | part | data-component-def-stmt; no proc-component-def-stmt |
| R737 | data-component-def-stmt | part | as a type-declaration-stmt (R801), DIMENSION the attribute a component uses; default initialization (R744's = expr) |
| R754 | derived-type-spec | part | type-name; no type-param-spec-list |
| R756 | structure-constructor | proved | derived-type-spec ( [component-spec-list] ), read as a function reference (R1520) and told apart by its name's declaration; the components in order, by keyword, then default-initialized (7.5.10) |
| R757 | component-spec | proved | [keyword =] component-data-source, read as an actual-arg-spec |
| R758 | component-data-source | proved | expr |
| R777 | array-constructor | part | lbracket ac-spec rbracket |
| R778 | ac-spec | part | ac-value-list |
| R779 | lbracket | proved | |
| R780 | rbracket | proved | |
| R781 | ac-value | proved | expr (not beginning with `(`: the subset's), ac-implied-do |
| R782 | ac-implied-do | proved | ( ac-value-list , ac-implied-do-control ) |
| R783 | ac-implied-do-control | proved | [integer-type-spec ::] ac-do-variable = scalar-int-expr , scalar-int-expr [, scalar-int-expr]; INTEGER [( [KIND =] k )] ::, the variable then of that kind (cases/acdotyped.f90: flang only, gfortran 16 rejects it) |
| R784 | ac-do-variable | proved | a construct entity (19.4) of the type of the variable of its name, which is integer (the meaning) |
| R801 | type-declaration-stmt | proved |  |
| R802 | attr-spec | proved | ALLOCATABLE, DIMENSION, INTENT, PARAMETER, SAVE, VALUE |
| R803 | entity-decl | proved | object-name [( array-spec )] [* char-length] [initialization], the char-length an int-literal-constant; in the meaning the entity is CHARACTER of that length (7.4.4.2), and a length on another type an error (8.2's constraint on * char-length) |
| R804 | object-name | proved |  |
| R805 | initialization | proved | = constant-expr |
| R814 | array-spec | proved | explicit-shape-spec-list, assumed-shape-spec-list, deferred-shape-spec-list |
| R815 | explicit-shape-spec | proved |  |
| R816 | lower-bound | proved |  |
| R817 | upper-bound | proved |  |
| R820 | assumed-shape-spec | proved |  |
| R822 | deferred-shape-spec | proved | `:`, read as an assumed-shape-spec without a lower bound; an ALLOCATABLE entity's in the meaning |
| R828 | intent-spec | proved | IN, OUT, INOUT, IN OUT |
| R840 | data-stmt | proved | DATA data-stmt-set [[,] data-stmt-set]..., a declaration-construct (fps :dsets); in the meaning a main program's DATA statements initialize its variables before its first statement (8.6.7), each value as by intrinsic assignment; a subprogram's are not in the meaning yet |
| R841 | data-stmt-set | proved | data-stmt-object-list / data-stmt-value-list / |
| R842 | data-stmt-object | proved | a variable (a primary: name, array element, substring or structure component, kept whole) or a data-implied-do; in the meaning a scalar, a whole array in array element order, or an array element |
| R843 | data-implied-do | part | read as an io-implied-do's list (fp :ilist), a superset; not in the meaning |
| R846 | data-stmt-value | proved | [data-stmt-repeat *] data-stmt-constant |
| R847 | data-stmt-repeat | proved | an int-literal-constant or a named constant; in the meaning nonnegative (C882) |
| R848 | data-stmt-constant | part | a literal, a named constant, a complex literal, [sign] an int or real literal; no structure-constructor or NULL() |
| R851 | dimension-stmt | proved | DIMENSION [::] entity-decl-list, each an array-name ( array-spec ), no initialization; in the meaning the array-spec joins the entity's declaration, or an implicitly typed one (8.7) |
| R855 | parameter-stmt | proved | PARAMETER ( named-constant-def-list ) (:parstmt), "parameter" now among *fkeywords*; in the meaning each named constant takes its earlier type declaration (moved to the statement, with the PARAMETER attribute) or its implicit type (8.7), its value converted as by assignment (fdecl's par-decls) |
| R856 | named-constant-def | proved | named-constant = constant-expr, read as an entity-decl (:ent) with an initialization only |
| R859 | save-stmt | proved | SAVE [[::] saved-entity-list], each an object-name (no common block); in the meaning, each saved entity's SAVE attribute (8.5.16) |
| R866 | implicit-stmt | proved | IMPLICIT NONE, IMPLICIT implicit-spec-list (read by imp-specs, proved with its own lemmas in fstmt-base.lisp); in the meaning a main program's or subprogram's undeclared names (a main program's DIMENSION'd names too) are typed by their first letter (8.7) |
| R867 | implicit-spec | proved | declaration-type-spec ( letter-spec-list ): INTEGER, REAL, LOGICAL, COMPLEX, DOUBLE PRECISION, CHARACTER [* char-length]; no kind-selector |
| R868 | letter-spec | proved | letter [- letter] |
| R901 | designator | proved | object-name, array-element, array-section |
| R902 | variable | proved | in assignment-stmt |
| R908 | substring | proved | parent-string ( substring-range ); a scalar name's is a part-ref of one triplet, told apart by its type |
| R909 | parent-string | part | scalar-variable-name, array-element, a named constant; no literal constant |
| R910 | substring-range | proved | [ scalar-int-expr ] : [ scalar-int-expr ] |
| R911 | data-ref | proved | part-ref [% part-ref]... |
| R912 | part-ref | proved | |
| R913 | structure-component | proved | data-ref; read and assigned (10.2.1.2), an array component's element or section read and assigned; an element of an array of structures |
| R917 | array-element | proved | |
| R918 | array-section | proved | |
| R919 | subscript | proved | |
| R921 | section-subscript | proved | subscript, subscript-triplet, vector-subscript |
| R922 | subscript-triplet | proved | |
| R924 | stride | proved | |
| R925 | vector-subscript | proved | int-expr, read as an expression; in the meaning, a rank-one integer array, its elements the indices (cases/vecsub.f90) |
| R929 | allocate-stmt | part | ALLOCATE ( allocation-list ); no type-spec, no alloc-opt (STAT=, ERRMSG=, SOURCE=): allocating an allocated variable stops the program (9.7.4) |
| R933 | allocation | part | allocate-object ( allocate-shape-spec-list ), read as an actual argument; the list required (no scalar allocatable), no coarray spec |
| R934 | allocate-object | part | variable-name; no structure-component |
| R935 | allocate-shape-spec | proved | [lower-bound-expr :] upper-bound-expr, read as a subscript or a triplet without stride |
| R936 | lower-bound-expr | proved |  |
| R938 | upper-bound-expr | proved |  |
| R944 | deallocate-stmt | part | DEALLOCATE ( allocate-object-list ); no dealloc-opt: deallocating an unallocated variable stops the program (9.7.4) |
| R1001 | primary | part | literal, designator, array-constructor, function-reference, ( expr ) |
| R1003 | level-1-expr | proved | no defined-unary-op |
| R1005 | mult-operand | proved | |
| R1006 | add-operand | proved | |
| R1007 | level-2-expr | proved | |
| R1008 | power-op | proved | |
| R1009 | mult-op | proved | |
| R1010 | add-op | proved | |
| R1011 | level-3-expr | proved | |
| R1012 | concat-op | proved | |
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
| R1107 | block-construct | proved | block-stmt [block-specification-part] block end-block-stmt; its entities a frame elaborated each time it runs |
| R1108 | block-stmt | part | BLOCK; no construct name |
| R1109 | block-specification-part | part | declaration-constructs (R507); in the meaning, type declarations only, none SAVE'd or initialized but a named constant |
| R1110 | end-block-stmt | part | END BLOCK; no construct name |
| R1119 | do-construct | proved |  |
| R1120 | do-stmt | proved | both forms |
| R1121 | label-do-stmt | proved | rewritten as a nonlabel DO before the units are read |
| R1122 | nonlabel-do-stmt | proved |  |
| R1123 | loop-control | part | do-variable = e, e [, e]; WHILE; CONCURRENT without concurrent-locality |
| R1124 | do-variable | proved |  |
| R1125 | concurrent-header | part | no scalar-mask-expr |
| R1126 | concurrent-control | proved |  |
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
| R1146 | case-expr | proved | integer, logical, character (the meaning) |
| R1147 | case-selector | proved | ( case-value-range-list ), DEFAULT |
| R1148 | case-value-range | proved | all four forms |
| R1149 | case-value | proved |  |
| R1159 | goto-stmt | proved |  |
| R1158 | exit-stmt | proved |  |
| R1161 | continue-stmt | proved |  |
| R1162 | stop-stmt | proved | STOP [stop-code]: an integer or character scalar expr (R1163, the meaning) |
| R1201 | io-unit | part | *, file-unit-number; no internal-file-variable (the unit * only, 5 or 6, in the meaning) |
| R1202 | file-unit-number | proved | |
| R1210 | read-stmt | proved | both forms |
| R1211 | write-stmt | proved | |
| R1212 | print-stmt | proved |  |
| R1213 | io-control-spec | part | [UNIT=], [FMT=], ADVANCE= (a literal); C1210, C1211, C1218, C1223; a format required (no unformatted I/O) |
| R1215 | format | part | *, a label, a char-literal-constant; no other default-char-expr |
| R1216 | input-item | part | variable (a designator, character included; not a substring in the meaning); no io-implied-do |
| R1217 | output-item | part | expr; no io-implied-do |
| R1301 | format-stmt | part | its format-specification one token (flex); read into edit descriptors by fio.lisp's parse-format, not proved |
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
| R1544 | stmt-function-stmt | part | read as R1033 assignment-stmt (the same tokens): in the meaning a main program's leading assignments name ( dummy-arg-name-list ) = expr, name not an array, are statement functions (15.6.4), typed by declaration or implicitly; each actual a scalar of its dummy's type and kind (a character's length too); a subprogram's are not in the meaning |
| R1545 | return-stmt | proved | no alternate return |
| R1546 | contains-stmt | proved |  |
