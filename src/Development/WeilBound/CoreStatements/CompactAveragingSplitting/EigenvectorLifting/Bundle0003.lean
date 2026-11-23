module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
section
noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Local

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Invertible (2 : k)]
  {K : Type} [CommRing K] [Algebra k K] (c : K →ₐ[k] K) {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ν] [DecidableEq ν] [Fintype κ]

def IsSkewM (J : Matrix β β K) : Prop := (∀ i j, c (J j i) = -J i j) ∧ IsUnit J.det

def IsEv (ψ : AddChar k ℂ) {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c (-1) JA JB) κ) (Cy : Matrix β ν K)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ z : Matrix α ν K, ∀ φ ∈ SB (κ → k), l (d.rho ψ (z * Cyᵀ) φ) = l φ

end Local

def AllLocal (Q : ∀ (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Invertible (2 : k)]
    (K : Type) [CommRing K] [Algebra k K] [TopologicalSpace K], (K →ₐ[k] K) → AddChar k ℂ → Prop) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (K : Type) [CommRing K] [Algebra k K] [TopologicalSpace K] [IsModuleTopology k K] (c : K →ₐ[k] K) (ψ : AddChar k ℂ),
    IsField K → (∃ ξ, IsQuad c ξ) → Continuous ψ → ψ ≠ 1 → Q k K c ψ

def SiegelTransport : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n N : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) om, IsHerm c JA → IsSkewM c JB →
    IsLagr c JB Cy → IsWeilB c (sbClass k) ψ (-1) JA JB d χ om → SiegelRule c (sbClass k) ψ (-1) JA JB d χ Cy om

def LinearAct : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n N : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) om l, IsHerm c JA → IsSkewM c JB →
    IsLagr c JB Cy → IsWeilPair c (sbClass k) ψ (-1) JA JB d χ 1 om → IsEv c ψ d Cy l →
    ∀ g, ∀ φ ∈ SB (κ → k), l (om (g, 1) φ) = l φ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}


variable (E) in
abbrev Ev (v : Pl F) : Type := Fv F v ⊗[F] E

def cV (σ : E →ₐ[F] E) (v : Pl F) : Ev E v →ₐ[Fv F v] Ev E v := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ

def locM {a b : Type} (J : Matrix a b E) (v : Pl F) : Matrix a b (Ev E v) := J.map (inclR (F := F) (Fv F v))

def IsLocChar (χ : Chr F E) (v : Pl F) (χv : (Ev E v)ˣ →* Circle) : Prop :=
  ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χv (Units.map (compFin F E v).toMonoidHom z) = χ z

structure IsLocPair {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (v : Pl F) [LocallyCompactSpace (Fv F v)] [Invertible (2 : Fv F v)] (ψv : AddChar (Fv F v) ℂ)
    (dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) (locM X.J v) (locM W.J v)) (Fin n × Fin d)) (χXv χWv : (Ev E v)ˣ →* Circle)
    (omv : UG (cV σ v) (locM X.J v) × UG (cV σ v) (locM W.J v) →* Module.End ℂ (Fn F n d v)) : Prop where
  psi : ∀ x, ψv x = psiLoc ψ v x
  chX : IsLocChar χX v χXv
  chW : IsLocChar χW v χWv
  weil : IsWeilPair (cV σ v) (sbClass (Fv F v)) ψv (-1) (locM X.J v) (locM W.J v) dv χXv χWv omv
  Heisenberg₂ : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ (dv.rho ψv (u.map (compFin F E v)) φ)
  surjX : ∀ gv : UG (cV σ v) (locM X.J v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (compFin F E v) = gv.1.1
  surjW : ∀ hv : UG (cV σ v) (locM W.J v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (compFin F E v) = hv.1.1
  loc : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∃ gv hv, (mat g).map (compFin F E v) = gv.1.1 ∧
    (mat h).map (compFin F E v) = hv.1.1 ∧ ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ ↔ φ₁ = omv (gv, hv) φ

def LocPairEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), PairOK B X W M om →
    M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) [LocallyCompactSpace (Fv F v)] [Invertible (2 : Fv F v)],
      ∃ ψv dv χXv χWv omv, IsLocPair M B.ψ χX χW om v ψv dv χXv χWv omv

end PositivityTheory.ThK
end
end

-- bundled from Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
section
noncomputable section

namespace PositivityTheory.ThK.SplitDict

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def intInd {m n : ℕ} (v : Pl F) : Matrix (Fin m) (Fin n) (Fv F v) → ℂ :=
  Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1

def DictAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (v : Pl F)
    (τ : E →ₐ[F] Fv F v) : Prop :=
  ∃ (b : GL (Fin a) (Fv F v)) (b' : GL (Fin a') (Fv F v)) (c : GL (Fin (a + a')) (Fv F v))
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (ι' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
    (gl : UA σ G.V.J → GL (Fin a) (Fv F v)) (gl' : UA σ G.V'.J → GL (Fin a') (Fv F v))
    (hl : UA σ G.W.J → GL (Fin (a + a')) (Fv F v)),
    G.M.IsLinW B.ψ τ b c ι ∧ G.M'.IsLinBar B.ψ τ b' c ι' ∧
    (∀ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩ → b = G.V.bas v ∧ b' = G.V'.bas v ∧ c = G.W.bas v) ∧
    ι (G.M.vac v) = intInd v ∧ ι' (G.M'.vac v) = intInd v ∧
    (∀ g ∈ UAt σ G.V (evFin F v), Reads v ι (om (g, 1)) (omA (chrW X.ν τ) (chrW X.β τ) (gl g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι (om (1, h)) (omA (chrW X.ν τ) (chrW X.β τ) 1 (hl h))) ∧
    (∀ g ∈ UAt σ G.V' (evFin F v), Reads v ι' (om' (g, 1)) (omB (chrW X.ν τ) (chrW X.α τ) (gl' g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι' (om' (1, h)) (omB (chrW X.ν τ) (chrW X.α τ) 1 (hl h))) ∧
    (∀ x, ∃ h ∈ UAt σ G.W (evFin F v), hl h = x)

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v),
      DictAt B G X om om' v τ

def IndIwasawa : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (α β : kˣ →* ℂˣ), ∀ F ∈ indSp a a' α β, (∀ h ∈ GlobalTheory.SplitWeil.KO k (Fin (a + a')), F h = 0) → F = 0

def RamNonzero : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ), HidaSetting a a' ϖ α β ν → ¬ IsUnram ν →
    ∃ Φ ∈ GlobalTheory.SplitWeil.SB _, pRam a a' ϖ ν β Φ ≠ 0

end PositivityTheory.ThK.SplitDict
end
end

