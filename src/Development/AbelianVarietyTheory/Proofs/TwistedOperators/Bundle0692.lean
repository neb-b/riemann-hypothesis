module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

theorem GlobalTheory.SquareAgree.exists_isOver : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
      IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∃ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
      IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' := by
  intro D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hωA hωB
  obtain ⟨p, q, hs, hz1, hz2⟩ := hT.sig
  have hev := hT.even
  have hrk := hT.rank
  let e : Fin X.rank ≃ Fin (W.rank + W₁.rank) := finCongr hT.rank
  obtain ⟨Bs, Xc, hψ, hα, hβ, hB, hXc, hemb, hκ⟩ := _root_.GlobalTheory.TripleBaseChars.exists_base_chars D ψ W W₁ X α β hT ωA hωA
  obtain ⟨V, V', Ws, hJV, hJV', hJW, hV, hV', hWs, hcart⟩ := _root_.GlobalTheory.PlaceSpaces.spaces_of_triple D W W₁ X A A₁ B α β hT p q hs e Bs hB hemb
  obtain ⟨cA, hcA⟩ := GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel D W X e (-1) (by norm_num)
  obtain ⟨cB, hcB⟩ := GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel D W₁ X e 1 one_ne_zero
  obtain ⟨hμ1, hd1⟩ := _root_.GlobalTheory.HaarConjImage.map_isHaarFD D W 1 hJV one_ne_zero ν 𝓕 hν
  obtain ⟨hμ2, hd2⟩ := _root_.GlobalTheory.HaarConjImage.map_isHaarFD D W₁ (-1) hJV' (by norm_num) ν₁ 𝓕₁ hν₁
  obtain ⟨M, hMμ, hMd, hM⟩ := _root_.GlobalTheory.SquareAgree.exists_good_model D Bs hB V Ws _ _ _ _ hV hWs _ _ hμ1 hd1
  obtain ⟨M', hMμ', hMd', hM'⟩ := _root_.GlobalTheory.SquareAgree.exists_good_model D Bs hB V' Ws _ _ _ _ hV' hWs _ _ hμ2 hd2
  have hJt : V.J = (if true then 1 else -1 : D.host.E) • W.gram := by simpa using hJV
  have hJf : V'.J = (if false then 1 else -1 : D.host.E) • W₁.gram := by simpa using hJV'
  have hct : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = (if true then 1 else -1 : ℂ) • A.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := fun w => by
    obtain ⟨τ, h1, h2, -, h4⟩ := hcart w
    exact ⟨τ, h1, by simpa using h2, h4⟩
  have hcf : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V'.θ w = (if false then 1 else -1 : ℂ) • A₁.cart τ ∧
      Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := fun w => by
    obtain ⟨τ, h1, -, h3, h4⟩ := hcart w
    exact ⟨τ, h1, by simpa using h3, h4⟩
  have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if true then -1 else 1 : D.host.E) • W.gram)) :
      Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by simpa using hcA u
  have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if false then -1 else 1 : D.host.E) • W₁.gram)) :
      Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by simpa using hcB u
  obtain ⟨hA1, hA2⟩ := _root_.GlobalTheory.SquareAgree.algVec_correspond D ψ θ hθ true W X A B e Bs hB hψ V Ws _ _ _ _ hJt hJW hV hWs hct M hM cA hcA'
  obtain ⟨hB1, hB2⟩ := _root_.GlobalTheory.SquareAgree.algVec_correspond D ψ θ hθ false W₁ X A₁ B e Bs hB hψ V' Ws _ _ _ _ hJf hJW hV' hWs hcf M' hM' cB hcB'
  obtain ⟨om, hom, hwA⟩ := _root_.GlobalTheory.SquareAgree.exists_weil_of_oriented D ψ θ hθ true W X A B e Bs hB hψ V Ws _ _ _ _ hJt hJW hV hWs hct M hM cA hcA' β (β / α) ωA hωA
  obtain ⟨om', hom', hwB⟩ := _root_.GlobalTheory.SquareAgree.exists_weil_of_oriented D ψ θ hθ false W₁ X A₁ B e Bs hB hψ V' Ws _ _ _ _ hJf hJW hV' hWs hcf M' hM' cB hcB' α (α / β) ωB hωB
  let Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank := ⟨p, q, V, V', Ws, M, M'⟩
  refine ⟨e, Bs, Γ, Xc, om, om', cA, cB, ?_, ?_⟩
  · exact
      { psi := hψ
        alpha := hα
        beta := hβ
        JW := hJV
        JW₁ := hJV'
        JX := hJW
        measW := hMμ
        domW := hMd
        measW₁ := hMμ'
        domW₁ := hMd'
        weilA := hwA
        weilB := hwB
        algA := hA1
        algA' := hA2
        algB := hB1
        algB' := hB2 }
  · refine ⟨hB, ?_, hXc, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hev
      exact
        { lt := by omega
          even := ⟨k, by omega⟩
          kappa := hκ
          eBig := by show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2; omega
          aBig := hz2
          hV := hV
          hV' := hV'
          hW := hWs
          hM := hM
          hM' := hM' }
    · show M.IsWeil Bs.ψ Xc.β (Xc.β / Xc.α) om
      rw [hα, hβ]; exact hom
    · show M'.IsWeil Bs.ψ Xc.α (Xc.α / Xc.β) om'
      rw [hα, hβ]; exact hom'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImageRevB

variable {D : D7}

theorem incM_mul {m : ℕ} (G H : Matrix (Fin m) (Fin m) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (G * H) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM H :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.mul_nonsing_inv _ hG, incM_one, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have e1 : ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [e1]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.nonsing_inv_mul _ hG, incM_one, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.DarbImageRevB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaGlobal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FockThetaOnto

variable {D : D7}

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    unfold GlobalTheory.TripleRead.ptO
    beta_reduce
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    show HMul.hMul ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) = x
    rw [h2, Matrix.mul_assoc, h1, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

theorem exists_darbAlg_of_mem_algF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig) (hψ : Bs.ψ = ψ)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
    (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : Vs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s')
    (hc : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = ((B.cart τ).submatrix e e).map conj)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ) (f : WO S X → ℂ) (hf : f ∈ algF ψ θ ε A B) :
    ∃ Φ ∈ GlobalTheory.TripleAssembly.darbAlg M Bs.ψ Bs.emb, GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e Φ = f := by
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hg : (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) =
      (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul]; rfl
    · simp only [if_true, neg_smul, one_smul]; exact neg_gram S
  obtain ⟨Φ, hΦ, hd⟩ := (_root_.GlobalTheory.SquareAgree.algVec_correspond D ψ θ hθ ε S X A B e.symm Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hc M hM
    (crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e)
    (fun u => by rw [← hg]; rfl)).1 f hf
  refine ⟨Φ, hΦ, funext fun x => ?_⟩
  have := hd.2 ((crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e).symm x)
  rw [AddEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.FockThetaOnto

end
end

