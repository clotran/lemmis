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
