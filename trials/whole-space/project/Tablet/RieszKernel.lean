module

public import Tablet.OneParticle

@[expose] public section

-- [TABLET NODE: RieszKernel]
noncomputable def RieszKernel {d : ℕ} (s ε : ℝ) (x : OneParticle d) : ℝ :=
-- BODY
  if ε = 0 then ‖x‖ ^ (-s) / s else (‖x‖ ^ 2 + ε ^ 2) ^ (-s / 2) / s
