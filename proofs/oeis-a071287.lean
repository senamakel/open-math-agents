import OMAStatements.S_oeis_a071287

open OMA.S_oeis_a071287

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) := by
  intro h
  have hbad : numeratorAt 6 6 ≠ gfCoeff 21 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2, 3, 4, 5, 2, 4, 6, 5, 3, 1, 5, 4, 3, 4, 2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 1] 6 := by
    decide
  exact hbad (h.2 6)
