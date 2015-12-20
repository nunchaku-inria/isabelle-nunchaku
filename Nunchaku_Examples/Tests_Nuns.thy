(*  Title:      HOL/Nunchaku_Examples/Tests_Nuns.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2009-2015

Nunchaku tests.
*)

section {* Nunchaku Tests *}

theory Tests_Nuns
imports Main
begin

ML {* () |> getenv "KODKODI" <> "" ? Nunchaku_Tests.run_all_tests *}

end
