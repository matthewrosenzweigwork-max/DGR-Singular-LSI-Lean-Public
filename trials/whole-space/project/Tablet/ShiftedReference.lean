import Tablet.OneParticle

-- [TABLET NODE: ShiftedReference]
def ShiftedReference {d : ℕ} (V b : OneParticle d → ℝ)
    (m : OneParticle d) : (OneParticle d → ℝ) × (OneParticle d → ℝ) :=
-- BODY
  (fun x => V (x + m) - V m, fun x => b (x + m))
