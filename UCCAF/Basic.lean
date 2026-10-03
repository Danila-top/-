import Mathlib

namespace UCCAF

/-- A normalized score used by UCCAF components. -/
def ValidScore (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 100

/-- UCCI as specified in the current UCCAF research protocol:
    UCCI = (IS + 2*CS) / 2. -/
def ucci (is cs : ℝ) : ℝ :=
  (is + 2 * cs) / 2

/-- KSI as specified in the current UCCAF research protocol:
    KSI = (IS + 2*CS + P) / 3. -/
def ksi (is cs p : ℝ) : ℝ :=
  (is + 2 * cs + p) / 3

theorem ucci_lower_bound
    {is cs : ℝ}
    (his : ValidScore is)
    (hcs : ValidScore cs) :
    0 ≤ ucci is cs := by
  rcases his with ⟨his0, his100⟩
  rcases hcs with ⟨hcs0, hcs100⟩
  dsimp [ucci]
  linarith

theorem ucci_upper_bound
    {is cs : ℝ}
    (his : ValidScore is)
    (hcs : ValidScore cs) :
    ucci is cs ≤ 150 := by
  rcases his with ⟨his0, his100⟩
  rcases hcs with ⟨hcs0, hcs100⟩
  dsimp [ucci]
  linarith

theorem ksi_lower_bound
    {is cs p : ℝ}
    (his : ValidScore is)
    (hcs : ValidScore cs)
    (hp : ValidScore p) :
    0 ≤ ksi is cs p := by
  rcases his with ⟨his0, his100⟩
  rcases hcs with ⟨hcs0, hcs100⟩
  rcases hp with ⟨hp0, hp100⟩
  dsimp [ksi]
  linarith

theorem ksi_upper_bound
    {is cs p : ℝ}
    (his : ValidScore is)
    (hcs : ValidScore cs)
    (hp : ValidScore p) :
    ksi is cs p ≤ 100 := by
  rcases his with ⟨his0, his100⟩
  rcases hcs with ⟨hcs0, hcs100⟩
  rcases hp with ⟨hp0, hp100⟩
  dsimp [ksi]
  linarith

theorem ksi_eq_100_of_all_100 :
    ksi 100 100 100 = 100 := by
  norm_num [ksi]

end UCCAF
