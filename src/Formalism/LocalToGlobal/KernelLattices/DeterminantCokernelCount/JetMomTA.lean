module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

abbrev Meas (q r : ℕ) [Fact q.Prime] : Type := C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]

section Stmts

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q])

variable {D cc δ q} (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)


variable (D cc δ q)

end Stmts

end Formalism.L2.Ker.I3.JetMomA
