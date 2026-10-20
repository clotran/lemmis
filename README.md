# Lemmis

*Formula translation, by means of premises.*

Lemmis is Fortran, extended with Clojure: every valid Fortran program
means what the Fortran standard says, and what Fortran never had --
immutable values, lazy sequences, functions as values, pipelines -- is
written in syntax Fortran never accepted.

    pure function energy(coords)
      energy = ->> coords map(norm) filter(positive?) sum
    end function

    do x in ->> naturals() map(square) take(10)
      print *, x
    end do

It is a library of [clotran](https://github.com/clotran/clotran) --
Clojure hosted on Fortran: a Lemmis file is read into Clojure forms,
which clotran evaluates, compiles to Fortran and calls Fortran packages
from, as it does its own.
Lemmis is clotran with Fortran's syntax, and its libraries work the same:

1. clotran libraries (`.cljf`, those using `fortran/` arrays and Fortran
   packages among them) work in Lemmis as in clotran; clotran's
   ahead-of-time compiler also translates them to Fortran modules that
   Lemmis code, or plain Fortran, uses directly (James: "clotran will
   translate to fortran which can be used in lemmis").
2. Pure Clojure libraries (`.clj`, `.cljc`, no Java interop), fetched as
   source by `:git/url` and `:git/sha`, work too, as they do in clotran.
3. Clojure libraries that use Java interop, and Maven jars, do not:
   clotran has no JVM and does not emulate one (its DEVIATIONS and
   PACKAGES.md say so).

The name: Latin *lemma*, from Greek λῆμμα, "something taken" -- a
premise, and in mathematics a proved step. *Lemmis*, by means of
premises: it takes Fortran's standard and Clojure's meaning as given,
its values are fixed once established, and its meaning is to rest on
lemmas proved in ACL2, as clotran's machine does. (The form follows the
first declension, as Latin sometimes declined Greek *-ma* nouns; the
classical one is *lemmatibus*.)

Nothing works yet, and nothing starts before clotran 1.0: what it is to
become, and in what order, is [PLAN.md](PLAN.md).

## License

EPL-2.0 (LICENSE).
