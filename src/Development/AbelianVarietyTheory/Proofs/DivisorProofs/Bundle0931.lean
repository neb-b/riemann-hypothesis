module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

theorem relIndex_ne_zero_of_finite {G Y : Type} [AddCommGroup G] (H K : AddSubgroup G) {R : Set Y} (hR : R.Finite)
    (rel : G → Y → Prop) (h1 : ∀ k ∈ K, ∃ r ∈ R, rel k r) (h2 : ∀ k k' r, rel k r → rel k' r → k - k' ∈ H) :
    H.relIndex K ≠ 0 := by
  haveI := hR.to_subtype
  choose f hf hf' using h1
  haveI : Finite (K ⧸ H.addSubgroupOf K) := by
    refine Finite.of_injective (fun q => (⟨f _ (Quotient.out q : K).2, hf _ _⟩ : R)) fun q q' h => ?_
    have h3 : f _ (Quotient.out q : K).2 = f _ (Quotient.out q' : K).2 := congrArg Subtype.val h
    have h4 := h2 _ _ _ (hf' _ (Quotient.out q : K).2) (h3 ▸ hf' _ (Quotient.out q' : K).2)
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact h4
  exact AddSubgroup.index_ne_zero_of_finite

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hle : B ≤ A)
    {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

theorem normOp_comm (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hi : idx A B ≠ 0)
    (L : M →ₗ[ℂ] M) (hL : ∀ x v, L (W x v) = W x (L v)) {e : M} (he : Fixes W A e) :
    normOp lam W A B (L e) = L (normOp lam W A B e) := by
  obtain ⟨n, f, hf, hu⟩ := ((sumOp_transversal h A B hB).2.1 hi).1
  have he' : Fixes W A (L e) := fun a ha => by rw [← hL, he a ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [normOp, normOp, ((sumOp_transversal h A B hB).1 _ he' _ f hf hu).1,
    ((sumOp_transversal h A B hB).1 _ he _ f hf hu).1, map_smul, map_sum]
  simp only [hL]

end Abstract

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idx_latF_ne_zero {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (B : Submodule (𝓞 D.host.E) (XF S T)) {N : ℕ} (hN : 0 < N) (hB : ∀ b ∈ B, N • b ∈ latF S T ΛS ΛT) :
    idx (latF S T ΛS ΛT) B ≠ 0 := by
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) N hN
  refine relIndex_ne_zero_of_finite _ _ hR
    (fun b r => ∃ u ∈ latO S T ΛS ΛT fun _ => True, N • (b : WO S T) = r + N • u) (fun b hb => h _ (hB b hb)) ?_
  rintro b b' r ⟨u, hu, h1⟩ ⟨u', hu', h2⟩
  have h3 : N • ((b : WO S T) - b') = N • (u - u') := by
    rw [nsmul_sub, nsmul_sub, h1, h2, add_sub_add_left_eq_sub]
  have h4 : (b : WO S T) - b' = u - u' := by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hN ((b : WO S T) - b'), h3, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN]
  show (b : WO S T) - b' ∈ latO S T ΛS ΛT fun _ => True
  rw [h4]
  exact sub_mem hu hu'

theorem idx_latF_eq (B : Submodule (𝓞 D.host.E) (XF S T)) :
    idx (latF S T LS LT) B = (latO S T LS LT fun _ => True).relIndex (B.toAddSubgroup.map (XF.incl S T)) :=
  AddSubgroup.relIndex_comap (latO S T LS LT fun _ => True) (XF.incl S T) B.toAddSubgroup

theorem phase_two (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) (w : 𝓞 D.host.E) {u : XF S T}
    (hu : u ∈ latF S T LS LT) : phase ψ w (2 • u) = 1 := by
  have h : ψ (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) = 1 :=
    (hA _).1 ((latF S T LS LT).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
    (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phase, h2]
  congr 2
  rw [← symplOH_add_self, ← symplOH_add_right, XF.coe_nsmul, two_nsmul]

theorem phase_half {e : AE D} (he : IsSplitIdem D e) (w : 𝓞 D.host.E) {u : XF S T} (hu : IsHalf e (u : WO S T)) :
    phase ψ w u = 1 := by
  have h : IsHalf e (intA D w • (u : WO S T)) := by
    rw [isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  rw [phase, symplOH, half_orth he h hu, mul_zero, neg_zero, AddChar.map_zero_eq_one]

theorem real_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) :
    realIdem D • mt V g = realIdem D • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => realIdem_mul_of_fin ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]
  rfl

theorem fin_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) :
    (1 - realIdem D) • mt V g = (1 - realIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero]
  refine Matrix.ext fun i j => (realIdem_mul_of_real ?_).symm
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPart D) (finPart D).map_zero (finPart D).map_one]
  rfl

theorem rhoF_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) (x : XF S T) :
    rhoF S T (g, h) x = x := by
  have h1 : ∀ y : XF S T, (1 - realIdem D) • (y : WO S T) = y := fun y => by
    rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]
  apply XF.ext
  rw [← h1 (rhoF S T (g, h) x), coe_rhoF, smul_actO (fin_smul_mt hg) (fin_smul_mt hh), h1]

theorem real_smul_real (u : WO S T) : (realIdem D • u).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * u i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_smul_fin (u : WO S T) : ((1 - realIdem D) • u).map (infPart D) = 0 := by
  funext i j
  show infPart D ((1 - realIdem D) * u i j) = 0
  rw [RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]

theorem off_smul_mt_place {V : HSp D} {η : AF D.host.F} {g : GA D V} (hg : SuppPl η V g) :
    (1 - algebraMap (AF D.host.F) (AE D) η) • mt V g =
      (1 - algebraMap (AF D.host.F) (AE D) η) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : algebraMap (AF D.host.F) (AE D) η • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem cA_algebraMap (η : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) η) = algebraMap (AF D.host.F) (AE D) η := by
  show η ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem exists_half_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : NonSplitAt D v η) :
    ∃ a : AE D, finPart D a ∈ intAE D ∧ 2 * a = algebraMap (AF D.host.F) (AE D) η := by
  obtain ⟨⟨α, rfl, h1, h0⟩, hn⟩ := h
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [h0 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    rw [← hα] at e3
    exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, h1, h0⟩, e3⟩, e3⟩
  obtain ⟨y, hy⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
  rw [map_ofNat] at hy
  have hy' : (2 : Fv D.host.F v) * y = 1 := congrArg Subtype.val hy
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v y), ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v y, 1, rfl⟩
  · rw [two_mul, ← map_add (f := _), ← map_add (f := _), ← two_mul, hy', hα]
    rfl

theorem finPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η) :
    finPart D (algebraMap (AF D.host.F) (AE D) η) ∈ intAE D := by
  obtain ⟨β, rfl, h1, h0⟩ := h
  refine AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem smooth_theta (hψ : IsCharAF D.host.F ψ) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) (hA : SelfDual (gamF ψ S T) (latF S T ΛS ΛT))
    (hlev : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ latO S T ΛS ΛT fun _ => True, N • u ∈ U) (f : thetaSub ψ S T) :
    ∃ B : Submodule (𝓞 D.host.E) (XF S T), idx (latF S T ΛS ΛT) B ≠ 0 ∧
      ∀ a ∈ latF S T ΛS ΛT, (∀ t ∈ B, gamF ψ S T a t = 1) → opF hψ S T w a f = f := by
  have H := isHeis_opF hψ S T hw
  obtain ⟨U, hU, hf⟩ := f.2.level
  obtain ⟨N, hN, hNU⟩ := hlev U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XF S T, (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • x) = x := fun x => by
    apply XF.ext
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • (x : WO S T)) = x
    rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN2]
  refine ⟨(latF S T ΛS ΛT).comap ((2 * N) • LinearMap.id), idx_latF_ne_zero hS hT _ hN2 fun b hb => hb,
    fun a _ ha => ?_⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF S T ΛS ΛT := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • t) ∈ latF S T ΛS ΛT
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opF, hf _ (by rw [XF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end GlobalTheory.FinWeilO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothStable

theorem rep_mem_sm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w ∈ M.sm τ, M.rep τ g w ∈ M.sm τ := by
  intro D V S M τ g hg w hw
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have e : M.sm τ = GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) :=
    Submodule.span_eq (GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
  rw [e] at hw ⊢
  exact GlobalTheory.SmVec.rep_mem (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ))
    (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hσ) hw hg

end GlobalTheory.SmoothStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOver
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.RepOver

noncomputable def coverOf {T : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i)) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J Z z (fun p => hc p) hz

theorem hom_eq_of_local {T S : Scheme.{0}} (t t' : T ⟶ S)
    (h : ∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧
      z ≫ t = z ≫ t') : t = t' := by
  choose Z z hz hp he using h
  exact Scheme.Cover.hom_ext (coverOf Z z hz (fun p => ⟨p, hp p⟩)) t t' he

theorem exists_glue {T S : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i))
    (t : ∀ i, Z i ⟶ S)
    (ht : ∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k →
      a ≫ t i = b ≫ t k) : ∃ t₀ : T ⟶ S, ∀ i, z i ≫ t₀ = t i :=
  ⟨Scheme.Cover.glueMorphisms (coverOf Z z hz hc) t
      (fun i k => ht i k _ _ _ pullback.condition),
    fun i => Scheme.Cover.ι_glueMorphisms (coverOf Z z hz hc) t _ i⟩

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)

theorem map_map {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a.left ≫ b.left = c.left)
    (d : F.obj (op Z)) : F.map a.op (F.map b.op d) = F.map c.op d := by
  have : c = a ≫ b := Over.OverMorphism.ext (by simpa using h.symm)
  subst this
  simp

theorem sig_eq {Y : Scheme.{0}} (r r' : Y ⟶ S) (h : r = r') (e : F.obj (op (Over.mk r)))
    (e' : F.obj (op (Over.mk r'))) (c : Over.mk r ⟶ Over.mk r') (hc : c.left = 𝟙 Y)
    (he : F.map c.op e' = e) :
    (⟨r, e⟩ : Σ t : Y ⟶ S, F.obj (op (Over.mk t))) = ⟨r', e'⟩ := by
  subst h
  have : c = 𝟙 _ := Over.OverMorphism.ext hc
  subst this
  subst he
  simp

noncomputable def tot : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun y =>
    ⟨f.unop ≫ y.1, F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact sig_eq F _ _ (Category.id_comp _) _ _ _ rfl rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    refine sig_eq F _ _ (Category.assoc _ _ _) _ _ (Over.homMk (𝟙 _) (by simp)) rfl ?_
    refine (map_map F _ _ (Over.homMk g.unop (Category.assoc _ _ _).symm) (by simp) _).trans ?_
    exact map_map F _ _ _ (by simp) _

def el {V : Over S} (v : F.obj (op V)) : (tot F).obj (op V.left) := ⟨V.hom, v⟩

theorem el_inj {V : Over S} {v v' : F.obj (op V)} (h : el F v = el F v') : v = v' :=
  eq_of_heq (Sigma.mk.inj h).2

theorem map_el {Y V : Over S} (a : Y ⟶ V) (v : F.obj (op V)) :
    (tot F).map a.left.op (el F v) = el F (F.map a.op v) :=
  sig_eq F (a.left ≫ V.hom) Y.hom (Over.w a) _ _ (Over.homMk (𝟙 _) (by simp)) rfl
    (map_map F _ _ _ (by simp) _)

theorem w_of_map_el {Y V : Over S} {a : Y.left ⟶ V.left} {v : F.obj (op V)} {y : F.obj (op Y)}
    (h : (tot F).map a.op (el F v) = el F y) : a ≫ V.hom = Y.hom :=
  congrArg Sigma.fst h

theorem w_of_map_eq {Y : Scheme.{0}} {V V' : Over S} {a : Y ⟶ V.left} {b : Y ⟶ V'.left}
    {v : F.obj (op V)} {v' : F.obj (op V')}
    (h : (tot F).map a.op (el F v) = (tot F).map b.op (el F v')) : a ≫ V.hom = b ≫ V'.hom :=
  congrArg Sigma.fst h

theorem map_eq_iff {Y V V' : Over S} (a : Y ⟶ V) (b : Y ⟶ V')
    (v : F.obj (op V)) (v' : F.obj (op V')) :
    (tot F).map a.left.op (el F v) = (tot F).map b.left.op (el F v') ↔
      F.map a.op v = F.map b.op v' := by
  rw [map_el, map_el]
  exact ⟨el_inj F, fun h => by rw [h]⟩

end GlobalTheory.RepOver


open GlobalTheory.RepOver in
theorem GlobalTheory.RepOver.representable_over : ∀ (S : Scheme.{0}) (F : (Over S)ᵒᵖ ⥤ Type 1), (∀ (T : Over S) (y y' : F.obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Over S) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Over S) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Over S) (y : F.obj (op T)), ∃ W : T.left.Opens, ∀ (Y : Over S) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a.left q ∈ W) → (∀ (T : Over S) (y : F.obj (op T)) (p : T.left), ∃ (i : Ix) (Y : Over S) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a.left ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Over S) (x₀ : F.obj (op B)), (∀ (T : Over S) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro S F hsep hglue Ix U x hmono hopen hcov
  refine Exists.elim (_root_.GlobalTheory.PicGlue.exists_represent_of_charts_large (tot F) ?_ ?_ Ix (fun i => (U i).left)
    (fun i => el F (x i)) ?_ ?_ ?_) ?_
  rotate_right
  · rintro B ⟨⟨tB, dB⟩, huniv, j, hj, hc, hx⟩
    refine ⟨Over.mk tB, dB, fun T y => ?_, fun i => Over.homMk (j i)
      (w_of_map_el F (V := Over.mk tB) (hx i)), hj, hc, fun i => ?_⟩
    · obtain ⟨g, hg, hu⟩ := huniv T.left (el F y)
      refine ⟨Over.homMk g (w_of_map_el F (V := Over.mk tB) hg), ?_, fun g' hg' => ?_⟩
      · exact el_inj F ((map_el F _ dB).symm.trans hg)
      · exact Over.OverMorphism.ext (hu g'.left ((map_el F g' dB).trans (congrArg (el F) hg')))
    · exact el_inj F ((map_el F _ dB).symm.trans (hx i))
  · rintro T ⟨t, d⟩ ⟨t', d'⟩ h
    obtain rfl : t = t' := hom_eq_of_local t t' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Z, z, hz, hp, congrArg Sigma.fst he⟩
    obtain rfl : d = d' := hsep (Over.mk t) d d' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Over.mk (z ≫ t), Over.homMk z rfl, hz, hp, (map_eq_iff F _ _ d d').1 he⟩
    rfl
  · intro T J Z z y hz hc hy
    obtain ⟨t, ht⟩ := exists_glue Z z hz hc (fun i => (y i).1)
      (fun i k Y a b hab => congrArg Sigma.fst (hy i k Y a b hab))
    obtain ⟨d, hd⟩ := hglue (Over.mk t) J (fun i => Over.mk (y i).1)
      (fun i => Over.homMk (z i) (ht i)) (fun i => (y i).2) hz hc
      (fun i k Y a b hab => (map_eq_iff F a b _ _).1
        (hy i k Y.left a.left b.left (congrArg (fun c => c.left) hab)))
    exact ⟨⟨t, d⟩, fun i => (map_el F (Y := Over.mk (y i).1) (V := Over.mk t)
      (Over.homMk (z i) (ht i)) d).trans (congrArg (el F) (hd i))⟩
  · intro i Y u u' h
    have := hmono i (Over.mk (u ≫ (U i).hom)) (Over.homMk u rfl)
      (Over.homMk u' (w_of_map_eq F h).symm) ((map_eq_iff F _ _ _ _).1 h)
    exact congrArg (fun c => c.left) this
  · rintro i T ⟨t, d⟩
    obtain ⟨W, hW⟩ := hopen i (Over.mk t) d
    refine ⟨W, fun Y a => Iff.trans ?_ (hW (Over.mk (a ≫ t)) (Over.homMk a rfl))⟩
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨Over.homMk u (w_of_map_eq F (V := Over.mk t) hu).symm, (map_eq_iff F _ _ _ _).1 hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u.left, (map_eq_iff F _ _ _ _).2 hu⟩
  · rintro T ⟨t, d⟩ p
    obtain ⟨i, Y, a, u, hp, h⟩ := hcov (Over.mk t) d p
    exact ⟨i, Y.left, a.left, u.left, hp, (map_eq_iff F _ _ _ _).2 h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_bound_smooth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := by
  first | (exact @GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (exact GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (intros; apply GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffine
section
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier


end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInverseGramLocalBasisIntegral
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem selfDual_inv_gram_integral (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hval : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) (s : 𝓞 E) (hs : s ∉ w.asIdeal)
    (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) (i k : Fin n) :
    w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  set G := Xᵀ * J * X.map σ with hGdef
  set a : Fin n → E := fun j => e * G⁻¹ i j with ha
  have haG : a ᵥ* G = fun j => if j = i then e else 0 := by
    have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    funext j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [Matrix.vecMul, dotProduct, ha, mul_assoc, ← Finset.mul_sum, h2]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  have key : ∀ c : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (X *ᵥ a) (X *ᵥ c) = e * σ (c i) := by
    intro c
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    have h1 : (fun j => σ ((X *ᵥ c) j)) = X.map σ *ᵥ (fun j => σ (c j)) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec, haG]
    simp [dotProduct]
  have hXX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have hXX' : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have hform_smul : ∀ (t : E) (u v : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (t • u) v = t * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J u v := by
    intro t u v
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    rw [smul_dotProduct, smul_eq_mul]
  set y : Fin n → E := (s : E) • (X *ᵥ a) with hy
  have hyL : y ∈ L := by
    refine (hL y).2 fun x hx o => ?_
    obtain ⟨r, hr⟩ := hsr x hx i
    have hx' : X *ᵥ (X⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x = e * (r : E) := by
      rw [hy, hform_smul, ← hx', key, ← hr]
      ring
    rw [h3]
    have h4 : (o : E) * (e * (r : E)) = ((o * r : 𝓞 E) : E) * e := by
      push_cast; ring
    rw [h4]
    exact he (o * r)
  have h5 := hval y hyL k
  have h6 : (X⁻¹ *ᵥ y) k = (s : E) * (e * G⁻¹ i k) := by
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
    rfl
  rw [h6, map_mul] at h5
  have hsv : w.valuation E (s : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hs
  rw [hsv, one_mul] at h5
  exact h5

end GlobalTheory
end

