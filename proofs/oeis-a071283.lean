import OMAStatements.S_oeis_a071283

open OMA.S_oeis_a071283

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071283.main) := by
  intro h
  have hbad : numeratorAt 4 4 ≠ gfCoeff 10 [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3, 2, 2, 1, 1, 1] 4 := by
    decide
  exact hbad (h.2 4)
