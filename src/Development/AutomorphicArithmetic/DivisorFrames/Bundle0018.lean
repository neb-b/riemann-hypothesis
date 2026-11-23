module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsSBHalfThetaOfSelfDualLattices
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0007
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftTripleLocalSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

theorem UpperTheory.thetaLift_triple_local_split_places :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ true A WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = -(A.gram.map (τ v) * X.rA.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinW ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdA (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)),
        X.vac = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f t = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hP hL t P τ hS b c ι hb hc hι hι0 φ hφ hφ' hφA g hvac
  have hPS : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v => by
    constructor
    · intro hv
      exact ⟨splitPrime (τ ⟨v, hv⟩), (hS _).2 ⟨_, rfl⟩, GlobalTheory.AdelicU.splitPrime_under (τ ⟨v, hv⟩)⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under (τ u)]
      exact u.2
  have hτS : ∀ v : P, splitPrime (τ v) ∈ S t := fun v => (hS _).2 ⟨v, rfl⟩
  have hinj : Function.Injective fun v : P => splitPrime (τ v) := fun u v h => by
    have h1 := GlobalTheory.AdelicU.splitPrime_under (τ u)
    have h2 := GlobalTheory.AdelicU.splitPrime_under (τ v)
    have h' : splitPrime (τ u) = splitPrime (τ v) := h
    exact Subtype.ext (h1.symm.trans (h' ▸ h2))
  obtain ⟨hh0, hh1⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hPS hτS
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (τ v)) * (G.map (incA D)).map (piW (τ v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hbG : ∀ v : P, ((b v)⁻¹).1 = ((G.map (incA D)).map (piW (τ v)) * X.rA.β.1.map (evW (τ v)))ᵀ := fun v => by
    have e0 : (G.map (incA D)).map (piW (τ v)) = -A.gram.map (τ v) := by
      refine Matrix.ext fun i j => ?_
      have e1 : G i j = -A.gram i j := by rw [hG]; rfl
      have e2 : ∀ y, piW (τ v) (incA D y) = τ v y := fun y => one_mul (τ v y)
      show piW (τ v) (incA D (G i j)) = -(τ v (A.gram i j))
      rw [e2, e1, map_neg]
    rw [hb, e0, Matrix.neg_mul, Matrix.transpose_neg]
  have key : ∀ (x : WO A WW) (v : P),
      ((b v)⁻¹).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (τ v)) * (GlobalTheory.SplitFlip.invT (c v)).1 =
      (((frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)))ᵀ).submatrix id (finCongr hr) := fun x v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (τ v)) =
        ((Matrix.map x (piW (τ v)) * (G⁻¹.map (incA D)).map (piW (τ v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)) =
        (X.rW.β⁻¹).1.map (evW (τ v)) * Matrix.map x (piW (τ v)) * X.rA.β.1.map (evW (τ v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact GlobalTheory.BotMatch.evW_toEAf (τ v) (x i j)
    rw [← hG, hbG, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (X.rW.β.1.map (evW (τ v))) _ ?_ (c v) (hc v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hth := hX.fst t
  rw [hvac] at hth
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ true A WW _ (finCongr hr) Bs Vs Ws M hP X.rA.Λ X.rW.Λ hL (selfDual_neg hX.rigA.1) hX.rigW.1
    P τ (fun v => (τ v).comp D.sp.cm.sig) (fun _ _ => rfl) (X.e t) hh0 hh1 (fun v => (b v)⁻¹)
    (fun v => GlobalTheory.SplitFlip.invT (c v)) ι (fun v => hι v) hι0 φ hφ hφ' g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t) (fun x => ?_) hth
  by_cases hx : IsHalf (X.e t) x
  · rw [if_pos hx]
    refine (UpperTheory.stdSectionFirst_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
      A'.rank hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [hφA v]
    exact congrArg _ (key x v).symm
  · rw [if_neg hx]
    exact if_neg fun h => hx h.1
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.TripleDualCoordSplitPlacesOfIsPairIsLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem piW_cA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) :
    piW t (cA D w) = piW (t.comp D.sp.cm.sig) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem piW_incA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (e : D.host.E) : piW t (incA D e) = t e := by
  change GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e
  simp

private theorem coord_eq {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (A' WW : HSp D) {d : ℕ} (e : Fin d ≃ Fin WW.rank)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) :
    (βA'⁻¹).1.map (evW t) * (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ * (βW.1.map (evW t)).submatrix e e =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t)).submatrix id e := by
  have hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.DualPairCheck.gram_star A' j i
  have h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (congrFun hG i) j
    change piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)
    rw [piW_incA', ← h]
    rfl
  have h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) =
      ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e := by
    rw [← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]
    rfl
  have h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e := by
    refine Matrix.ext fun i j => ?_
    simp
  have hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E),
      ((M.map (incA D)).map (toEAf D)).map (evW t) = M.map t := by
    intro p q M
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, GlobalTheory.BotMatch.evW_toEAf, piW_incA']
  have hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (evW t) =
      ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.transpose_apply, GlobalTheory.BotMatch.evW_toEAf, piW_cA']
  have hxi : evW t (eToEAf D D.host.xi0) = t D.host.xi0 := by
    rw [← piW_incA' t, ← GlobalTheory.BotMatch.evW_toEAf]
    rfl
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t) =
      t D.host.xi0 • ((βA'⁻¹).1.map (evW t) * ((A'.gram⁻¹).map t *
        ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (evW t)) := by
    rw [← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul]
    refine Matrix.ext fun i j => ?_
    exact map_mul (evW t) _ _
  rw [h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_assoc]
  rfl

theorem UpperTheory.triple_dualCoord_split_places_of_isPair_isLat :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A'.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ false A' WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA'.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A'.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A'.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinBar ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdB (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank)),
        X.vac' = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f' t = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hp hl t P τ hS b c ι hb hc hι h1 φ hφ hφP hstd g hvac
  have hP : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v =>
    ⟨fun hv => ⟨_, (hS _).2 ⟨⟨v, hv⟩, rfl⟩, GlobalTheory.AdelicU.splitPrime_under _⟩, by
      rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under]
      exact u.2⟩
  have hinj : Function.Injective (fun v : P => splitPrime (τ v)) := fun u v h =>
    Subtype.ext ((GlobalTheory.AdelicU.splitPrime_under (τ u)).symm.trans
      ((congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h).trans (GlobalTheory.AdelicU.splitPrime_under (τ v))))
  obtain ⟨hh1, hh0⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hP fun v => (hS _).2 ⟨v, rfl⟩
  have hdet : ∀ v : P, ((Ws.J.map (τ v))ᵀ).det ≠ 0 := fun v => by
    have h0 : Ws.J.det ≠ 0 := by
      rw [hp.JW, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) (GlobalTheory.LatVac.gram_det_isUnit WW).ne_zero
    rw [Matrix.det_transpose]
    have h2 := (τ v).toRingHom.map_det Ws.J
    exact fun h => h0 ((τ v).toRingHom.injective ((h2.trans h).trans (map_zero _).symm))
  have hbb : ∀ v : P, -((b v).1ᵀ * Vs.J.map (τ v)) = (X.rA'.β⁻¹).1.map (evW (τ v)) := fun v => by
    have e1 : Vs.J.map (τ v) = -(A'.gram.map (τ v)) := by
      rw [hp.JV]
      refine Matrix.ext fun i j => ?_
      simp
    have e2 : (b v).1ᵀ * (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v))) = 1 := by
      rw [← Matrix.transpose_transpose (A'.gram.map (τ v) * _), ← hb v, ← Matrix.transpose_mul, Units.inv_mul,
        Matrix.transpose_one]
    have e3 : X.rA'.β.1.map (evW (τ v)) * (X.rA'.β⁻¹).1.map (evW (τ v)) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e1, Matrix.mul_neg, neg_neg, ← Matrix.mul_one (_ * A'.gram.map (τ v)), ← e3, ← Matrix.mul_assoc,
      Matrix.mul_assoc (b v).1ᵀ, e2, Matrix.one_mul]
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ false A' WW _ (finCongr hr) Bs Vs Ws M hp X.rA'.Λ X.rW.Λ hl hX.rigA'.1 hX.rigW.1 P
    (fun v => (τ v).comp D.sp.cm.sig) τ (fun v x => congrArg (τ v) (star_star x).symm) (cA D (X.e t)) hh0
    (fun z => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hh1 z)
    (fun v => Matrix.GeneralLinearGroup.map (evW (τ v)) X.rA'.β⁻¹)
    (fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet v) * c v) ι (fun v => ?_) h1 φ hφ hφP g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (X.e t) (X.ideal S t) A.rank A' WW X.rA'.β X.rW.β) (X.f' t) (fun x => ?_) ?_
  · have h := hι v
    unfold Model.IsLinBar at h
    convert h using 1
    funext u
    change (X.rA'.β⁻¹).1.map (evW (τ v)) * _ * ((Ws.J.map (τ v))ᵀ * (c v).1) = _
    rw [← hbb v]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  · by_cases hx : IsHalf (cA D (X.e t)) x
    · rw [if_pos hx]
      refine (UpperTheory.stdSectionSecond_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A.rank A' WW
        X.rA'.β X.rW.β hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
      rw [hstd v, ← coord_eq, ← hc v, ← hp.JW, Matrix.mul_assoc]
      rfl
    · rw [if_neg hx]
      exact if_neg fun h => hx h.1
  · rw [← hvac]
    exact hX.snd t
end

