import OMAStatements.S_oeis_a071281

open OMA.S_oeis_a071281

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071281.main) := by
  intro h
  have hbad : numeratorAt 3 3 ≠ gfCoeff 6 [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 1, 2, 1, 1] 3 := by
    decide
  exact hbad (h.2 3)
