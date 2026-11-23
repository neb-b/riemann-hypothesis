module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCase
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Abstract

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d d' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
  {U : Matrix (Fin d) κ C} {L : Matrix κ (Fin d) C}

theorem cut_diagonal (hLU : L * U = 1) {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) :
    L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j = Matrix.diagonal fun b => t (j b) := by
  have h : L * (U * Matrix.diagonal t * L) * U = Matrix.diagonal t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLU, Matrix.one_mul, Matrix.mul_assoc, hLU, Matrix.mul_one]
  have h2 : L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j =
      (L * (U * Matrix.diagonal t * L) * U).submatrix j j := by
    ext a b; simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [h2, h, Matrix.submatrix_diagonal _ _ hj]; rfl

theorem proj_eq {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) (h1 : ∀ b, t (j b) = 1)
    (h0 : ∀ ℓ, (¬ ∃ b, j b = ℓ) → t ℓ = 0) :
    U.submatrix id j * L.submatrix j id = U * Matrix.diagonal t * L := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_of_injOn j hj.injOn (fun _ _ => by simp) (fun ℓ _ hℓ => ?_) fun b' _ => by rw [h1, mul_one]
  rw [h0 ℓ (by simpa using hℓ), mul_zero, zero_mul]

theorem diagonal_mulVec (hLU : L * U = 1) (t : κ → C) (ℓ : κ) :
    (U * Matrix.diagonal t * L).mulVec (fun e => U e ℓ) = t ℓ • fun e => U e ℓ := by
  have h : U * Matrix.diagonal t * L * U = U * Matrix.diagonal t := by rw [Matrix.mul_assoc, hLU, Matrix.mul_one]
  funext e
  have := congrFun (congrFun h e) ℓ
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem coord_mulVec (hLU : L * U = 1) (j : Fin d' → κ) (ℓ : κ) (b : Fin d') :
    (L.submatrix j id).mulVec (fun e => U e ℓ) b = if j b = ℓ then 1 else 0 := by
  have := congrFun (congrFun hLU (j b)) ℓ
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem intSpan_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (u : β → Fin d → C) :
    intSpan v (fun a => u (e a)) = intSpan v u := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e.symm k), fun k => ha _, by rw [← e.sum_comp]; simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e k), fun k => ha _, by rw [← e.sum_comp]⟩

theorem nonempty_muAction (G : LogFGL v d) (p h : ℕ) (ty : Fin d → ZMod h)
    (hz : ∀ z : C, z ^ (p ^ h - 1) = 1 → ∃ φ, IsIntHom G G φ (Matrix.diagonal fun b => z ^ p ^ (ty b).val)) :
    Nonempty (MuAction G p h ty) := by
  classical
  choose φ hφ using hz
  refine ⟨⟨fun z => if hz : z ^ (p ^ h - 1) = 1 then φ z hz else 0, fun z hz a => ?_, fun z a => ?_, fun z hz a => ?_⟩⟩
  · rw [dite_eq_left hz]; exact (hφ z hz).2.1 a
  · split_ifs with hz
    · exact (hφ z hz).1 a
    · simp
  · rw [dite_eq_left hz, (hφ z hz).2.2 a]
    simp [Matrix.diagonal_apply, ite_smul]

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} [Fact p.Prime]

theorem exists_orbit (X : ValExt T p) (hp : UnramIn E p) (τ : E →+* ℂ) :
    ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
      (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) ∧
      ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1 := by
  obtain ⟨-, h, h0, hc⟩ := GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card E H l c p T io X τ
  haveI := charP_residueField_of_irreducible X
  obtain ⟨hon, F, Fp, Fs, Fi, Fk⟩ := _root_.GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist (𝓞 E) _ p (red io X τ) h h0 (by rw [← primeBelow_eq_ker]; exact hc)
  obtain ⟨hi, hs⟩ := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose lab hlab using fun s => hs (F s)
  refine ⟨h, h0, hc, lab, ⟨hi ?_, fun s a => ?_, fun s s' e => Fi ?_, fun σ => ?_⟩, fun s a => ?_, fun z hz => ?_⟩
  · rw [hlab]; ext a; rw [Fp]; simp
  · rw [← red_eq_pow_iff, hlab, hlab, Fs]
  · rw [← hlab, ← hlab, e]
  · rw [primeBelow_eq_ker, primeBelow_eq_ker, Fk]
    exact exists_congr fun s => by rw [← hlab, hi.eq_iff]
  · rw [← red_eq_pow_iff, hlab, Fp]
  · have hq : p ^ h - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h0.ne' (Fact.out : p.Prime).one_lt)
    obtain ⟨z', hz'⟩ := X.ints.exists_of_le_one
      ((isIntV_iff X z).1 (le_of_eq (v_eq_zero_of_pow_eq_one hq hz).symm))
    have h1 : z' ^ p ^ h = z' := X.ints.hom_inj (by
      rw [map_pow, hz', ← Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_sub_ne_zero hq)), pow_succ, hz, one_mul])
    obtain ⟨a, ha⟩ := hon (residue X.O z') (by rw [← map_pow, h1])
    refine ⟨a, ?_⟩
    rw [← hz', ← algebraMap_embO, ← residue_eq_iff_v]
    exact ha

variable [StarRing (𝓞 E)] {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)

theorem exists_hom_of_approx [DecidableEq (Lt1 Dw)] {L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C}
    (hL : ∀ a b, IsIntV (vX_vp X) (L a b)) (hUL : (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1)
    (t : (E →+* ℂ) → X.C) (ht : ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ, (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t σ)) :
    ∃ φ, IsIntHom (fgl Ch X) (fgl Ch X) φ
      ((Matrix.of fun e ℓ => lieVec Ch X ℓ e) * Matrix.diagonal (fun ℓ : Lt1 Dw => t ℓ.1) * L) := by
  refine _root_.GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit X.C (vX_vp X) _ (fgl Ch X) (Lt1 Dw) _ L (fun e ℓ => isIntV_jX X _) hL hUL _ fun r => ?_
  obtain ⟨a, ha⟩ := ht r
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integers_act_integralChart_eigenDirections E H Dw l Xo c p T io X y Ch a
  exact ⟨fun ℓ => embX io X ℓ.1 a, _, _, h1, h2, fun ℓ => ha ℓ.1⟩

theorem typedPartAt (hp : UnramIn E p) (τ : E →+* ℂ) : TypedPartAt Ch X τ := by
  classical
  obtain ⟨h, h0, hc, lab, horb, hpow, hroot⟩ := exists_orbit (io := io) X hp τ
  haveI : NeZero h := ⟨h0.ne'⟩
  obtain ⟨L, hL, hLU, hUL⟩ := _root_.GlobalTheory.PrimePart.exists_integral_inverse_lieVec E H Dw l Xo c p T io X y Ch hp
  set U : Matrix (Fin (chD Ch.ch)) (Lt1 Dw) X.C := Matrix.of fun e ℓ => lieVec Ch X ℓ e with hU
  obtain ⟨-, -, hinj, hker⟩ := id horb

  let t : X.C → (E →+* ℂ) → X.C := fun z => Function.extend lab (fun s => z ^ p ^ s.val) 0
  have ht1 : ∀ z s, t z (lab s) = z ^ p ^ s.val := fun z s => hinj.extend_apply _ _ s
  have ht0 : ∀ z σ, (¬ ∃ s, lab s = σ) → t z σ = 0 := fun z σ hσ => Function.extend_apply' _ _ σ hσ
  have happ : ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ,
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t z σ) := by
    intro z hz r
    obtain ⟨a, h1, h2⟩ := _root_.GlobalTheory.PrimePart.exists_approx_root_twists E H l c p T io X τ h h0 lab hpow z hz (hroot z hz) r
    refine ⟨a, fun σ => ?_⟩
    by_cases hσ : ∃ s, lab s = σ
    · obtain ⟨s, rfl⟩ := hσ
      rw [ht1]; exact h1 s
    · rw [ht0 z σ hσ, sub_zero]; exact h2 σ fun e => hσ ((hker σ).1 e)

  let K := Σ s : ZMod h, Fin (Dw.mult (lab s))
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let j₀ : K → Lt1 Dw := fun k => ⟨lab k.1, k.2⟩
  have hj₀ : Function.Injective j₀ := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ hk
    obtain rfl : s = s' := hinj (congrArg Sigma.fst hk)
    obtain rfl : k = k' := eq_of_heq (Sigma.mk.inj hk).2
    rfl
  let j : Fin (Fintype.card K) → Lt1 Dw := fun b => j₀ (e b)
  have hj : Function.Injective j := hj₀.comp e.injective
  have hjr : ∀ ℓ : Lt1 Dw, (∃ s, lab s = ℓ.1) → ∃ b, j b = ℓ := by
    rintro ⟨σ, k⟩ ⟨s, rfl⟩
    exact ⟨e.symm ⟨s, k⟩, congrArg j₀ (e.apply_symm_apply _)⟩
  have hIP : U.submatrix id j * L.submatrix j id = U * Matrix.diagonal (fun ℓ : Lt1 Dw => t 1 ℓ.1) * L :=
    proj_eq hj _ (fun b => by rw [show (j b).1 = lab (e b).1 from rfl, ht1, one_pow])
      fun ℓ hℓ => ht0 1 _ fun hs => hℓ (hjr ℓ hs)
  have hPI : L.submatrix j id * U.submatrix id j = 1 := by
    have := cut_diagonal hLU hj (fun _ => 1)
    rwa [Matrix.diagonal_one, Matrix.mul_one, hUL, Matrix.mul_one, Matrix.diagonal_one] at this
  have hco : (1 : Matrix _ _ X.C) - U.submatrix id j * L.submatrix j id =
      U * Matrix.diagonal (fun ℓ : Lt1 Dw => 1 - t 1 ℓ.1) * L := by
    rw [hIP, ← Matrix.diagonal_sub, Matrix.diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUL]
  obtain ⟨G', ⟨ι', hι⟩, ⟨π', hπ⟩⟩ := GlobalTheory.T.logarithmic_group_law_split_by_idempotent X.C (vX_vp X) _ _ (fgl Ch X) (U.submatrix id j) (L.submatrix j id)
    (fun a b => isIntV_jX X _) (fun a b => hL _ _) hPI
    (by rw [hIP]; exact exists_hom_of_approx Ch X hL hUL (t 1) (happ 1 (one_pow _)))
    (by
      rw [hco]
      refine exists_hom_of_approx Ch X hL hUL (fun σ => 1 - t 1 σ) fun r => ?_
      obtain ⟨a, ha⟩ := happ 1 (one_pow _) r
      refine ⟨1 - a, fun σ => ?_⟩
      rw [map_sub (embX io X σ), map_one, sub_sub_sub_cancel_left, AddValuation.map_sub_swap]
      exact ha σ)
  have hfix : ∀ ℓ : Lt1 Dw, (U.submatrix id j * L.submatrix j id).mulVec (lieVec Ch X ℓ) =
      t 1 ℓ.1 • lieVec Ch X ℓ := fun ℓ => by
    rw [hIP]; exact diagonal_mulVec hLU _ ℓ
  have hco' : ∀ (ℓ : Lt1 Dw) b, (L.submatrix j id).mulVec (lieVec Ch X ℓ) b = if j b = ℓ then 1 else 0 :=
    fun ℓ b => coord_mulVec hLU j ℓ b
  let q : ∀ s, {b : Fin (Fintype.card K) // (e b).1 = s} ≃ Fin (Dw.mult (lab s)) := fun s =>
    (e.subtypeEquiv (q := fun k : K => k.1 = s) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype s)
  have hq : ∀ s b, j b.1 = ⟨lab s, q s b⟩ := by
    rintro s ⟨b, rfl⟩; rfl
  refine ⟨h, h0, hc, lab, horb, _, G', fun b => (e b).1, U.submatrix id j, L.submatrix j id,
    ⟨⟨ι', hι⟩, ⟨π', hπ⟩, hPI, fun ℓ => ⟨fun hℓ => ?_, fun hℓ => ?_⟩⟩, nonempty_muAction _ _ _ _ fun z hz => ?_,
    fun s => ?_, fun s => ?_, fun s f hf => ⟨⟨fun a b => ?_, ?_⟩, fun a b hb => ?_, fun k => le_antisymm ?_ ?_⟩⟩
  · obtain ⟨s, hs⟩ := (hker _).1 hℓ
    rw [hfix, ← hs, ht1, one_pow, one_smul]
  · rw [hfix, ht0 1 _ fun hs => hℓ ((hker _).2 hs), zero_smul]
  · obtain ⟨φ, hφ⟩ := exists_hom_of_approx Ch X hL hUL (t z) (happ z hz)
    have := isIntHom_comp hι (isIntHom_comp hφ hπ)
    rw [cut_diagonal hLU hj] at this
    exact ⟨_, by simpa only [show ∀ b, (j b).1 = lab (e b).1 from fun _ => rfl, ht1] using this⟩
  · rw [← intSpan_equiv (q s)]
    congr 1
    funext b
    rw [← hq]; rfl
  · rw [Fintype.card_congr (q s), Fintype.card_fin, Dw.rank, Nat.add_sub_cancel]
    unfold Datum.mult InPsi
    congr
  · beta_reduce; rw [frame, hco']; unfold IsIntV; split_ifs <;> simp
  · choose r hr using fun a : Fin (rk f) => hjr ⟨f.1, Fin.castLE (rk_le f) a⟩ ⟨s, hf.symm⟩
    refine ⟨r, ?_⟩
    have : (Matrix.of fun a b => (L.submatrix j id).mulVec (frame Ch X f a) (r b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, frame, hco', hr, Matrix.one_apply]
      simp [eq_comm]
    rw [this]; simp
  · rw [frame, hco', if_neg]
    intro hb'
    exact hb (hinj ((congrArg Sigma.fst hb').trans hf))
  · exact _root_.GlobalTheory.DepthMono.detDepth_le_of_isIntHom X.C _ _ _ _ k _ _ _ _ hπ _
  · have := _root_.GlobalTheory.DepthMono.detDepth_le_of_isIntHom X.C _ _ _ _ k _ _ _ _ hι fun a => (L.submatrix j id).mulVec (frame Ch X f a)
    simp only [Matrix.mulVec_mulVec, frame, hfix, hf, ht1, one_pow, one_smul] at this
    exact this

theorem formalGroupTypes : FormalGroupTypes := fun E _ _ _ H _ l _ c _ _ p _ hp T io X =>
  ⟨_root_.GlobalTheory.PrimePart.frobOnType_all E H l c p T io X, fun _ Ch τ => typedPartAt Ch X hp τ⟩

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift

namespace GlobalTheory.GalOne

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rec

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev zAt : Fam (Wc D i) := x0Mat (R.MW i σ)

def ConjW (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  OverK σ ∧ ChiAt R i σ μ' ∧ IsEtaConj σ R.eta η' ∧ IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧
    IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f

end Rec

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}


variable (T R i) in
abbrev OM : Type 1 := OMDat T.toCore R i Unit (fun _ => A.μ0)

abbrev Pinned (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : OM T R i) : Prop :=
  O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)

abbrev sOf (O : OM T R i) (σ' : O.c'.F →+* ℂ) : T.Q.c.F →+* ℂ := σ'.comp (incF T.Q.c O.c' O.hle)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev dictS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) :
    GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) s).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) s)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev muS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) : GA D (Wc D i) → ℂ := castDict hV (T.mu ((i : ℕ) + 1) s)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev xS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (h : GA D (Wc D i)) : Data D.host.E D.R.r :=
  (T.U ((i : ℕ) + 1) s).X (dictS hV h).1

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OM T R i) (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ)

def FactsAt : Prop :=
  res T σ = sOf O σ' ∧ GoodEmb T.Q.c (sOf O σ') ∧ GoodEmb O.c' σ' ∧
    (∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
    IsONeg (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    cart (R.MW i σ) = cartZ (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    (∀ ρ, T.x₀ ((i : ℕ) + 1) (sOf O σ') (tauE D ρ) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (zAt R i σ ρ)) ∧
    (∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ) ∧
    ∀ μ' η' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → IsEtaConj σ R.eta η' →
      (∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, MuVal (Wc D i) μ' (muS hV)) ∧
      (∀ v ε, NonSplitAt D v ε → UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹)) ∧ HypConj R i σ μ' η'

def PointAt (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i) (h : GA D (Wc D i)) : Prop :=
  ∃ γ ∈ GQ (Wc D i), ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (xS hV h).Ψ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' (xS hV h) g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hx : (dictS hV h).2 ∈ (xS hV h).dom),
    IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) (xS hV h) eT Dc.bas ∧ Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e ∧
    (xS hV h).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ SelfD (xS hV h) (xS hV h).Λ ∧
    latW (rank_Wc i) (xS hV h).Λ = latG (Wc D i) (γ * h) ∧
    (dictS hV h).2 = frOf (rank_Wc i) eT (mvZ R.θ (γ * h) (zAt R i σ)) ∧
    letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
    (∃ (A₀ : AnFib (xS hV h) Dc.bas Dc.idx Dc.e (dictS hV h).2 (xS hV h).Λ
        (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A₀.Reads 1 (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩).s th ∧
        MeanOne (xS hV h) Dc.bas Dc.idx (dictS hV h).2 (xS hV h).Λ th) ∧
    ∀ (g' : ℕ) (bas : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (xS hV h).Λ) (idx : Fin g' ≃ (xS hV h).Ψ × Fin D.R.r)
      (e : Fin g' ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSympl (xS hV h) bas → Matched T.Q.c (sOf O σ') (xS hV h) idx e →
      ∀ (A₁ : AnFib (xS hV h) bas idx e (dictS hV h).2 (xS hV h).Λ
          (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩))
        (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ a, mk a ∈ (xS hV h).Λ) →
        MarkAd (rank_Wc i) T.Q.l (iotaW T i) (γ * h) mk → A₁.Marked mk

def FrAtEmb (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ : WO (Vc D i) (Wc D i) → ℂ)
    (cc : (T.U ((i : ℕ) + 1) (sOf O σ')).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) ω f₀ (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV) (muS hV) (zAt R i σ) cc

def TermAt (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (ε : ℤˣ) : Prop :=
  ∀ (h : O.Cl' () → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
    RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) →
    ∀ (k : O.Cl' ()) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r),
      IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q →
      ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' →
      ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v →
      ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ))) (a • v) (ω (1, g') f₀) →
      ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) →
        MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) g' mk₂ →
      ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E,
        IsRoots (O.dδ ()).l₂ L ((ε : ℤ) • mk₂) (O.Nc () k) Y →
        GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) ∧
        Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ)))
          ((a * σ' (O.ep () k * ((((O.La () k).mIdx (O.Nc () k) D.R.r : O.c'.F))⁻¹ *
            ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : O.c'.F))⁻¹ *
            ((O.La () k).zCard (O.Nc () k) D.R.r : O.c'.F)))) •
            gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) (ω (h k, g') f)

def IsUp (x : VsV D i D.what₂.LL) (x' : VsV D i O.c'.F) : Prop :=
  (x' : Pol O.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map O.jL (x : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank)

def IsLtAt (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((relab O.c' σ' ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lt ℓ).1) ∧
      ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))

def IoAt {c : CoefA (Vc D i)} (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (f : WO (Vc D i) (Wc D i) → ℂ)
    (Λ : c.W → WO (Vc D i) (Wc D i) → ℂ) (ph : ℂ) : Prop :=
  ∀ x x', IsUp O x x' → ∃ Q : PolF D (Wc D i).rank (Vc D i).rank,
    Λ (c₁ x) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) f Q ∧
    ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))),
      (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q =
        MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) *
          MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io x'))

def CovAt (c0 : ℂ) : Prop :=
  letI : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
  ∀ y₂ : FrPt (O.dδ ()).Xo₂ (O.dδ ()).c₂ ℂ, evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ (O.dδ ()).cδ y₂ = c0

end GlobalTheory.GalOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensQuad

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  rcases eq_or_ne i w with rfl | h
  · simp
  · simp [Function.update_of_ne h]

noncomputable def atPlLin (w : T) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem atPlLin_apply (w : T) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := rfl

theorem atPl_mul (w : T) (L₁ L₂ : Module.End ℂ (V w)) : atPl w (L₁ * L₂) = atPl w L₁ * atPl w L₂ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod, Module.End.mul_apply]

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod]

theorem qop_atPl {ι : Type} [Fintype ι] [DecidableEq ι] (w : T) (F : ι → ι → Module.End ℂ (V w)) (α β : ℂ) (i j : ι) :
    qop (fun a b => atPl w (F a b)) α β i j = atPl w (qop F α β i j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qop, ← atPlLin_apply, map_sub, map_sum, map_smul, apply_ite (atPlLin w), map_zero]
  simp only [atPlLin_apply, atPl_mul, atPl_one]

theorem mem_of_atPl (C : ∀ w, Submodule ℂ (V w)) (w : T) (L : Module.End ℂ (V w)) (hL : ∀ x, L x ∈ C w)
    (v : ⨂[ℂ] i, V i) : atPl w L v ∈ tensAny C := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, atPl_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨w, by simpa using hL (f w)⟩, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.HoweR.TensQuad

open GlobalTheory.HoweR.TensQuad in
theorem GlobalTheory.HoweR.quadMod_actAt : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  intro T _ _ V _ _ C w p q a α β α' β' h i j v _
  have hu : units (actAt w a) = fun i j => atPl w (units a i j) := rfl
  have hn : negT (units (actAt w a)) = fun i j => atPl w (negT (units a) i j) := by
    funext i j
    simp only [negT, units, actAt_apply, ← atPlLin_apply, map_neg]
  refine ⟨?_, ?_⟩
  · rw [hu, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).1) v
  · rw [hn, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).2) v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCaseStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ h) π := by
  first | exact @GlobalTheory.NoethLiftObj.liftObj_of_noetherian | exact GlobalTheory.NoethLiftObj.liftObj_of_noetherian | (intros; apply GlobalTheory.NoethLiftObj.liftObj_of_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbit
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobOrbit

theorem hasDerivAt_sobCont_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 :=
  fun _ _ _ _ _ _ _ hu hπ _ hv _ hℓ _ hX =>
    (GlobalTheory.UnitarySmVec.smFam_orbit hu hπ hv hX).hasDerivAt_form hu hπ hℓ

end GlobalTheory.SobOrbit
end

