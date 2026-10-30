import Mathlib
set_option autoImplicit false

namespace AffineWordLog
noncomputable def coeff (a : ℝ) : List Bool → ℝ × ℝ
  | [] => (0, 1)
  | false :: w =>
      let c := coeff a w
      (1 - a * c.1, -a * c.2)
  | true :: w =>
      let c := coeff a w
      ((a / (1 + a)) * c.1, (a / (1 + a)) * c.2)
end AffineWordLog

set_option autoImplicit false

namespace AffineWordLog
noncomputable def J (x : ℝ) : ℝ :=
  if x = 0 then 0 else -Real.log (1 - x) / x - 1
end AffineWordLog

set_option autoImplicit false

namespace AffineWordLog
noncomputable def I (a : ℝ) : ℝ :=
  ∑' w : List Bool, J (a * (coeff a w).2 / (1 - a * (coeff a w).1))
end AffineWordLog
