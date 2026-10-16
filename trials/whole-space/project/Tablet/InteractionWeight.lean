import Tablet.PairInteraction
import Tablet.CollisionSet

-- [TABLET NODE: InteractionWeight]
noncomputable def InteractionWeight {d N : ℕ} (s coupling ε : ℝ)
    (X : ParticleConfig d N) : ℝ := by
-- BODY
  classical
  exact if coupling = 0 then 1 else
    if ε = 0 ∧ X ∈ CollisionSet d N then 0 else Real.exp (-PairInteraction s coupling ε X)
