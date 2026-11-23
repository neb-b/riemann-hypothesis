module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0015
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
public import Formalism.LocalToGlobal.GlobalTheory.PassageBaseSymmetricLevels
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem emb_mul' (g g' : D.R.GG) (x : D.host.E) :
    D.host.emb (g * g') x = D.host.emb g (D.host.sigmaOf g' x) := by
  simp only [Host.emb, Host.sigmaOf, map_mul, RingHom.comp_apply]
  rfl

theorem conj_comp_emb (g : D.R.GG) :
    (starRingEnd ℂ).comp (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  ext x
  rw [RingHom.comp_apply, emb_mul', ← D.host.conjE_apply (D.host.emb g)]
  rfl

theorem cc_mul_cc : D.R.cc * D.R.cc = 1 := by
  simp [Formalism.HC.Frame.cc, c0, Prod.ext_iff]

theorem ArchLab.emb_eq (A : ArchLab D) (τ : D.what₂.Tau) :
    A.emb τ = D.host.emb ((D.eTau (A.perm τ)).1 * (if A.side then 1 else D.R.cc)) := by
  rcases A with ⟨p, s⟩
  cases s
  · simp [ArchLab.emb, tauE, conj_comp_emb]
  · simp [ArchLab.emb, tauE]

theorem emb_injective : Function.Injective (D.host.emb) := (factEmb D.R D.host).1.1

theorem snd_side (b : Bool) : ((if b then 1 else D.R.cc : D.R.GG)).1.2 = if b then 1 else -1 := by
  cases b <;> rfl

theorem labExists : LabExists D := by
  intro σ
  obtain ⟨γ, hγ⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have hlab : ∀ τ, labE σ τ = D.host.emb (γ * (D.eTau τ).1) := by
    intro τ
    ext x
    rw [emb_mul', hγ]
    rfl
  by_cases hγP : γ ∈ D.R.Psi
  · let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1, mul_mem hγP (D.eTau τ).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel e1))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), true⟩, fun τ => ?_⟩
    rw [hlab τ]
    simp [ArchLab.emb, tauE, f]
  · have hnot : ∀ τ, γ * (D.eTau τ).1 ∉ D.R.Psi := by
      intro τ hm
      apply hγP
      have h1 : (γ * (D.eTau τ).1).1.2 = 1 := hm
      have h2 : (D.eTau τ).1.1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
      show γ.1.2 = 1
      simpa [Prod.fst_mul, Prod.snd_mul, h2] using h1
    have hmem : ∀ τ, γ * (D.eTau τ).1 * D.R.cc ∈ D.R.Psi := by
      intro τ
      have h1 := hnot τ
      rw [Formalism.HC.Frame.mem_Psi_iff] at h1 ⊢
      show (γ * (D.eTau τ).1).1.2 * (-1) = 1
      rcases Int.units_eq_one_or (γ * (D.eTau τ).1).1.2 with h | h
      · exact absurd h h1
      · rw [h]; rfl
    let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1 * D.R.cc, hmem τ⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel (mul_right_cancel e1)))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), false⟩, fun τ => ?_⟩
    rw [hlab τ, ArchLab.emb_eq]
    simp only [Equiv.ofBijective_apply, f, Equiv.apply_symm_apply, Bool.false_eq_true, if_false]
    rw [mul_assoc (γ * (D.eTau τ).1), cc_mul_cc, mul_one]

end Formalism.IndefR.Conj

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CutPassage3S
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

def CutPassage3S : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A3.fam3.Ok3 s → A3.fam3.TypesSep3 →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A3.side3 P0 ψ0 X.zs).Pos → (A3.side3 P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) →
    X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    (∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ) → GEquiv3 A3 X gE →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A3.A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPassA
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Bridge

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {U : Type} [AddCommGroup U] [Module K U]

theorem epOp_eq_epP (σ : Representation K G U) (P : Subgroup G) (ψ : P →* Kˣ) (χ : P →* (𝓞 K)ˣ)
    (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.epOp σ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.epP P χ σ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp Formalism.IndefR.TransferLatticeStatement.epP
  simp only [hχ]
  congr
  exact Subsingleton.elim _ _

theorem nOf_eq_nS {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.nS τ P χ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.TransferLatticeStatement.nS
  first
  | (unfold Formalism.IndefR.IndefiniteEpsilonOperator.epSp; rw [epOp_eq_epP τ P ψ χ hχ])
  | (simp only [Formalism.IndefR.IndefiniteEpsilonOperator.epSp, epOp_eq_epP τ P ψ χ hχ])
  | (rw [← epOp_eq_epP τ P ψ χ hχ]; rfl)

end Bridge

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

end In

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPassGood
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GoodPlacesAlt

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem sum_chars_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ Xc)
    {M : Type} [AddCommMonoid M] (F : (G → K) → M) :
    ∑ t, F (Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = ∑ χ ∈ Xc, F χ := by
  classical
  have himg : Finset.univ.image (fun t => Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = Xc := by
    ext χ
    rw [hX χ]
    simp
  rw [← himg, Finset.sum_image (fun s _ t _ h => hinj s t h)]

theorem mulVec_sum_smul {n : ℕ} (c : G → K) (M : G → Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (∑ g, c g • M g) *ᵥ x = ∑ g, c g • (M g *ᵥ x) := by
  classical
  have key : ∀ s : Finset G, (∑ g ∈ s, c g • M g) *ᵥ x = ∑ g ∈ s, c g • (M g *ᵥ x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ← ih]
      first
        | rw [Matrix.smul_mulVec]
        | rw [Matrix.smul_mulVec_assoc]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key Finset.univ

theorem cpt_sum_smul (σ : K →+* ℂ) {n : ℕ} (c : G → K) (y : G → Fin n → K) :
    cpt σ (∑ g, c g • y g) = ∑ g, σ (c g) • cpt σ (y g) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cpt, Finset.sum_apply, map_sum]

theorem sum_eq_one_of {E : Type} [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (ρ : G → Matrix (Fin n) (Fin n) K)
    (act : G → E →ₗ[ℂ] E) (hρ : ∀ g x, f (cpt σ (ρ g *ᵥ x)) = act g (f (cpt σ x)))
    (c : G → K) (hfix : ∀ x, ∑ g, σ (c g) • act g (f (cpt σ x)) = f (cpt σ x)) :
    ∑ g, c g • ρ g = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  have h1 : f (cpt σ ((∑ g, c g • ρ g) *ᵥ x)) = f (cpt σ x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mulVec_sum_smul, cpt_sum_smul, map_sum]
    simp only [map_smul, hρ]
    exact hfix x
  have h2 := hf h1
  funext i
  exact σ.injective (congrFun h2 i)

end GoodPlacesAlt

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

end In

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DatumVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev EAf (D : D7) : Type := D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F

def toEAf (D : D7) : AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp (finPart D)

def eToEAf (D : D7) : D.host.E →+* EAf D := Algebra.TensorProduct.includeLeftRingHom

def frMapO (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βT⁻¹).val ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D))) βS.val

def frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (x : WO S T) : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
      (T.gram.map (incA D))).map (toEAf D)))
    βT.val

def IsIntM {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) : Prop :=
  ∀ i j, N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E


open Classical in
def redM (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) :
    Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) :=
  fun i j => if h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨N i j, h⟩ else 0

def topL {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Matrix (Fin k) (Fin k) κ :=
  fun i j => if h : i.val < b ∧ j.val < a then y ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

def LowZero {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Prop :=
  ∀ i j, k ≤ i.val → j.val < k → y i j = 0


open Classical in
def omegaG {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
      ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
        (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
        (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H then
    ((L.P.chi ⟨fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (h.2.choose PP), h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
        ((L.cg (c + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (c + 1) (h.2.choose PP)) : ℂˣ) : ℂ)) *
      ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (h.2.choose PP))) : ℂˣ) : ℂ)⁻¹
  else 0


open Classical in
def omegaQ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then
    ∏ PP ∈ Q.attach, (((ξ PP.1 (h PP.1 PP.2).2.unit) : ℂˣ) : ℂ) ^ k
  else 0


open Classical in
def omegaK {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1 then 1 else 0

def IsIdemSum (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) ∧ e = ∑ PP ∈ P, es PP) ∧
    e * cA D e = 0


open Classical in
def IsStepVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) *
          omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
        else 0) f


open Classical in
def IsThPVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
        else 0) f

def pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] (WO S T → ℂ) :=
  pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f

def PlaceModelExistsSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
      (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧
      ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm


open Classical in
def StepVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint LS.Pg Q →
    (∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f


open Classical in
def ThPVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q →
    (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f

def VecLaw {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (KS : Subgroup (GA D S))
    (chS : GA D S → ℂ) (KT : Subgroup (GA D T)) (chT : GA D T → ℂ) (f : WO S T → ℂ) : Prop :=
  (∀ κ ∈ KS, om (κ, 1) f = chS κ • f) ∧ ∀ κ ∈ KT, om (1, κ) f = chT κ • f

end Formalism.IndefR.Datum

end
end

