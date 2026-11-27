import OMAStatements.S_oeis_a071285

open OMA.S_oeis_a071285

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071285.main) := by
  intro h
  have hbad : numeratorAt 5 5 ≠ gfCoeff 15 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2, 4, 5, 3, 1, 4, 3, 2, 3, 2, 1, 2, 1, 1, 1] 5 := by
    decide
  exact hbad (h.2 5)
