module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContractsOfConstant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic

namespace GlobalTheory.Cartier

namespace CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] (k : Type) [Field k] [Algebra k X.functionField]
  (D : CartierDiv X) (V : Set X.functionField)

def IsBasePoint (x : X) : Prop := ∀ f ∈ V, ¬ D.GeneratesAt x f

structure BasePointFree : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_generatesAt : ∀ x, ∃ f ∈ V, D.GeneratesAt x f

def VanishesOn (f : X.functionField) (Z : Set X) : Prop := ∀ x ∈ Z, D.VanishesAt x f

def ratioField : IntermediateField k X.functionField :=
  IntermediateField.adjoin k {r | ∃ f ∈ V, ∃ g ∈ V, g ≠ 0 ∧ r = f / g}

structure Birational : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_ne_zero : ∃ f ∈ V, f ≠ 0

  ratioField_eq : ratioField k V = ⊤

def SameImage (y y' : X) : Prop :=
  ∀ (n : ℕ) (b : Fin n → X.functionField), (∀ i, b i ∈ V) →
    ∀ (d : ℕ) (g : MvPolynomial (Fin n) k), g.IsHomogeneous d →
      ((d • D).GeneratesAt y (aeval b g) ↔ (d • D).GeneratesAt y' (aeval b g))

def Contracts (C : Set X) : Prop :=
  ∀ y ∈ C, ∀ y' ∈ C, ¬ D.IsBasePoint V y → ¬ D.IsBasePoint V y' → D.SameImage k V y y'

structure NoContract (bd : Set X) : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  not_contracts : ∀ C : Set X, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
    Disjoint C bd → ¬ D.Contracts k V C

variable {k D V}

theorem BasePointFree.not_isBasePoint (h : D.BasePointFree V) (x : X) : ¬ D.IsBasePoint V x :=
  fun hx => have ⟨f, hf, h'⟩ := h.2 x; hx f hf h'

theorem BasePointFree.exists_ne_zero (h : D.BasePointFree V) : ∃ f ∈ V, f ≠ 0 :=
  have ⟨f, hf, h'⟩ := h.2 (genericPoint X); ⟨f, hf, h'.ne_zero⟩

theorem IsEqn.generatesAt_aeval_iff {x : X} {u : X.functionFieldˣ} (h : D.IsEqn x u) {ι : Type}
    (b : ι → X.functionField) {d : ℕ} {g : MvPolynomial ι k} (hg : g.IsHomogeneous d) :
    (d • D).GeneratesAt x (aeval b g) ↔ UnitAt x (aeval (fun i => b i * u) g) := by
  have e := Twist.eval₂Hom_unit_mul (algebraMap k X.functionField) u b
    (mem_polyGrading_natCast.2 hg)
  rw [(h.nsmul d).generatesAt_iff, mul_comm, ← zpow_natCast]
  simp only [mul_comm (b _)]
  exact iff_of_eq (congrArg _ e.symm)

theorem contracts_of_constant (hk : ∀ (x : X) (c : k), RegAt x (algebraMap k X.functionField c))
    (hV : ∀ f ∈ V, f ∈ Set.range (algebraMap k X.functionField)) (C : Set X) :
    D.Contracts k V C := by
  have hu (x : X) (c : k) : UnitAt x (algebraMap k X.functionField c) ↔ c ≠ 0 :=
    ⟨fun h e => h.ne_zero (by rw [e, map_zero]), fun h =>
      (unitAt_iff ((map_ne_zero _).2 h)).2 ⟨hk x c, map_inv₀ (algebraMap k X.functionField) c ▸ hk x _⟩⟩
  have key (y : X) (hy : ¬ D.IsBasePoint V y) : D.IsEqn y 1 := by
    obtain ⟨f, hf, h⟩ : ∃ f ∈ V, D.GeneratesAt y f := by simpa [IsBasePoint] using hy
    obtain ⟨c, rfl⟩ := hV f hf
    have := (generatesAt_zero_iff.2 ((hu y c).2 fun e => h.ne_zero (by
      rw [e, map_zero])).inv).mul h
    rw [zero_add, inv_mul_cancel₀ h.ne_zero] at this
    exact not_not.1 (notMem_supp_iff.2 this)
  intro y _ y' _ hy hy' n b hb d g hg
  choose c hc using fun i => hV _ (hb i)
  rw [(key y hy).generatesAt_aeval_iff b hg, (key y' hy').generatesAt_aeval_iff b hg]
  simp only [Units.val_one, mul_one, ← hc]
  have e := aeval_algebraMap_apply X.functionField c g
  rw [Function.comp_def] at e
  rw [e, hu, hu]

end CartierDiv

namespace Presents

open CartierDiv

variable {k : Type} [Field k] {S : LinSys k} [IsIntegral S.Y] [Algebra k S.Y.functionField]
  [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] {D : CartierDiv S.Y}
  {r : S.L.ι → S.Y.functionFieldˣ} (h : Presents D S.L r)

def ratSet : Set S.Y.functionField := Set.range fun j => h.rat (S.b j)


omit [Algebra k S.Y.functionField] [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] in
theorem mem_of_mem_ratSet : ∀ f ∈ h.ratSet, f ∈ D.sections := by
  rintro _ ⟨j, rfl⟩
  exact h.rat_mem _


omit [Algebra k S.Y.functionField] [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] in
theorem basePointFree_iff : D.BasePointFree h.ratSet ↔ S.BasePointFree := by
  refine ⟨fun hb => eq_top_iff.2 fun x _ => ?_, fun hb => ⟨h.mem_of_mem_ratSet, fun x => ?_⟩⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hb.2 x
    exact Opens.mem_iSup.2 ⟨j, (h.generatesAt_rat_iff _).1 hj⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hb.ge (Set.mem_univ x))
    exact ⟨_, ⟨j, rfl⟩, (h.generatesAt_rat_iff _).2 hj⟩

theorem generatesAt_aeval_iff {d : ℕ} {g : MvPolynomial (Fin S.N) k} (hg : g.IsHomogeneous d)
    (x : S.Y) : (d • D).GeneratesAt x (aeval (fun j => h.rat (S.b j)) g) ↔
      x ∈ nonzeroLocus (S.form hg) := by
  obtain ⟨i, hi⟩ := exists_chart S.isLB x
  have e : aeval (fun j => h.rat (S.b j) * r i) g =
      fnOf _ (gen_mem hi) (Twist.zfun (S.form hg) i) := by
    rw [LinSys.form, Twist.zfun_formSec, Twist.chartEval, map_eval₂Hom, aeval_def, coe_eval₂Hom]
    congr 1
    · exact RingHom.ext fun a => (IsScalarTower.algebraMap_apply k Γ(S.Y, ⊤) _ a).trans
        (fnOf_resG le_top _ _).symm
    · exact funext fun j => (h.rat_mul _ i (gen_mem hi)).trans
        (fnOf_resG le_rfl (gen_mem hi) _).symm
  rw [(h.isEqn i x hi).generatesAt_aeval_iff _ hg, e, unitAt_fnOf_iff hi, Twist.basicOpen_zfun]
  exact and_iff_right hi

theorem sameImage_iff (y y' : S.Y) : D.SameImage k h.ratSet y y' ↔ S.SameImage y y' := by
  refine ⟨fun e d g hg => ?_, fun e n b hb d g hg => ?_⟩
  · rw [← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff]
    exact e _ _ (fun j => ⟨j, rfl⟩) d g hg
  · choose σ hσ using hb
    have := e d _ (hg.rename_isHomogeneous (f := σ))
    rwa [← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff, aeval_rename,
      show (fun j => h.rat (S.b j)) ∘ σ = b from funext hσ] at this

theorem noContract_iff (hb : S.BasePointFree) (bd : Set S.Y) :
    D.NoContract k h.ratSet bd ↔ S.NoContract bd := by
  have hn := (h.basePointFree_iff.2 hb).not_isBasePoint
  have e (C : Set S.Y) : D.Contracts k h.ratSet C ↔ S.Contracts C :=
    forall₄_congr fun y _ y' _ => by rw [imp_iff_right (hn y), imp_iff_right (hn y'), sameImage_iff]
  exact ⟨fun c C h₁ h₂ h₃ h₄ => (e C).not.1 (c.2 C h₁ h₂ h₃ h₄),
    fun c => ⟨h.mem_of_mem_ratSet, fun C h₁ h₂ h₃ h₄ => (e C).not.2 (c C h₁ h₂ h₃ h₄)⟩⟩

end Presents

end GlobalTheory.Cartier
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential
section
noncomputable section

namespace GlobalTheory.Mem.ColsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_potential {G A X : Type} [Group G] [CommGroup A] (χ : G →* A) (r : G → X → X → Prop)
    (h1 : ∀ x, r 1 x x) (hi : ∀ g x y, r g x y → r g⁻¹ y x)
    (hm : ∀ g g' x y z, r g x y → r g' y z → r (g' * g) x z) (hs : ∀ g x, r g x x → χ g = 1) :
    ∃ φ : X → A, ∀ g x y, r g x y → (φ x)⁻¹ * φ y = χ g := by
  let s : Setoid X := ⟨fun x y => ∃ g, r g x y, fun x => ⟨1, h1 x⟩, fun ⟨g, h⟩ => ⟨_, hi _ _ _ h⟩,
    fun ⟨g, h⟩ ⟨g', h'⟩ => ⟨_, hm _ _ _ _ _ h h'⟩⟩
  have hb : ∀ x, ∃ g, r g (Quotient.mk s x).out x := fun x => Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun g x y h => ?_⟩
  have e : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, h⟩
  have h2 := hm _ _ _ _ _ (hm _ _ _ _ _ (hc x) h) (hi _ _ _ (hc y))
  rw [← e] at h2
  have h3 := hs _ _ h2
  simp only [map_mul, map_inv] at h3
  rw [inv_mul_eq_one] at h3
  show (χ (c x))⁻¹ * χ (c y) = χ g
  rw [h3, mul_comm (χ g), inv_mul_cancel_left]

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice L hfg hsp γ hγ

section Host

variable {R : Ranks} (H : Host R)

def chi : letI := H.cmStar; unitary H.E →* ℂˣ :=
  letI := H.cmStar
  ∏ τ : Tau R, ((Units.map (H.emb ((τ : R.Psi) : R.GG) : H.E →* ℂ)).comp
    Unitary.toUnits)⁻¹

theorem chi_apply : letI := H.cmStar; ∀ z : unitary H.E, ((chi H z : ℂˣ) : ℂ) =
    ∏ τ : Tau R, (H.emb ((τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  intro z
  simp [chi]

private theorem prod_sigmaOf (x : H.E) :
    ∏ τ : Tau R, H.sigmaOf ((τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.galois
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  have hm : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ => ⟨_, hm σ⟩) ⟨fun a b h => ?_, fun τ => ?_⟩ _ _ (fun σ => ?_)
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val h))
  · have h1 : H.sigmaOf τ H.sqd = H.sqd := (H.galE_mem_Psi_iff _).1 (by simpa [Host.sigmaOf] using τ.2)
    have h2 : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h1
      | algebraMap y => exact AlgEquiv.commutes _ y
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
      | inv y _ hy => rw [map_inv₀, hy]
      | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    refine ⟨IntermediateField.fixingSubgroupEquiv H.K ⟨_, h2⟩, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply _
  · simp [Host.sigmaOf]

theorem chi_of_integral : letI := H.cmStar; ∀ z : unitary H.E, IsIntegral ℤ (z : H.E) → chi H z = 1 := by
  letI := H.cmStar
  intro z hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star (z : H.E) * z = 1 := z.2.1
    have h2 : φ (star (z : H.E)) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  apply Units.ext
  rw [chi_apply]
  have h := congrArg H.φ₀ (prod_sigmaOf H (z : H.E))
  rw [H.der.norm_mu z ⟨n, hn, hp⟩, map_one, map_one, map_prod] at h
  rw [Finset.prod_inv_distrib, Units.val_one, inv_eq_one]
  exact h

theorem exists_pot (N : ℕ) : letI := H.cmStar; ∃ φ : SDLat H.E N → ℂˣ,
    ∀ (γ : Matrix.unitaryGroup (Fin N) H.E) (L L' : SDLat H.E N),
      L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      (φ L)⁻¹ * φ L' = chi H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  letI := H.cmStar
  let dt : Matrix.unitaryGroup (Fin N) H.E →* unitary H.E :=
    { toFun := fun γ => ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hone : ∀ L : Submodule (𝓞 H.E) (Fin N → H.E), SDLat.smulLat (1 : Matrix (Fin N) (Fin N) H.E) L = L := by
    intro L
    ext v
    simp [SDLat.smulLat]
  have hmul : ∀ (a b : Matrix (Fin N) (Fin N) H.E) (L : Submodule (𝓞 H.E) (Fin N → H.E)),
      SDLat.smulLat (a * b) L = SDLat.smulLat a (SDLat.smulLat b L) := by
    intro a b L
    unfold SDLat.smulLat
    rw [← Submodule.map_comp, Matrix.toLin'_mul]
    rfl
  refine exists_potential ((chi H).comp dt)
    (fun γ (L L' : SDLat H.E N) => L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1)
    (fun L => (hone _).symm) (fun γ L L' h => ?_) (fun γ γ' L L' L'' h h' => ?_) (fun γ L h => ?_)
  · rw [h, ← hmul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact (hone _).symm
  · rw [h', h, ← hmul]; rfl
  · refine chi_of_integral H _ (isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)
    rw [h]
    exact ⟨v, hv, rfl⟩

end Host

section Chain

open GlobalTheory.MemberTorsor

variable (B : Pre)

def uI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero


open Classical in
@[reducible] def ch (u : B.Word) : ColumnChain B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { chain B.R (Tau B.R) (B.hcW u) (B.T u) with
    rhoDet := fun i _ => ((uI⁻¹ * uI ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rhoDet' := fun i _ => ((uI * uI ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rho_norm := fun _ _ _ => by simp [uI]
    rho'_norm := fun _ _ _ => by simp [uI] }


open Classical in
@[reducible] def member (u : B.Word) : Member B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { C := ch B u
    A := { atT B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) with
      duStar := B.duStar u, duStar_pos := B.duStar_pos u, Dstar := B.Dstar, Dstar_pos := B.Dstar_pos,
      GamP := B.GamP, one_lt_gammaP := B.one_lt_gammaP }
    P := { period B.R (Tau B.R) (B.hcW u) (B.T u) with } }

@[reducible] def cols0 : Cols0 B where
  mem := member B
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).L0
  clsLat_lat := letI := B.host.cmStar; fun _ i _ => baseLattice_full (B.sp.X i)
  Tup := Fin 3
  mu0 := 0
  muStar := 1
  muStar' := 2
  chTw u _ := ch B u
  memberColumns_twistedChain_base _ := rfl
  e0Tw _ _ := LinearEquiv.refl ℂ _
  PTw u _ := (member B u).P
  Dt := ℂˣ
  detCls _ _ _ := uI
  muTil _ := MonoidHom.id _
  chiD := MonoidHom.id _
  UO := ⊥
  chiD_UO x hx := Subgroup.mem_bot.1 hx
  e1Dt := chi B.host
  rest_detCharacter_on_unitary_eq := chi_apply B.host
  relDet N L L' := QuotientGroup.mk (((exists_pot B.host N).choose L)⁻¹ * (exists_pot B.host N).choose L')
  relDet_self N L := by simp
  relDet_mul N L L' L'' := by
    rw [← QuotientGroup.mk_mul, mul_assoc, mul_inv_cancel_left]
  relDet_smul N L L' γ h := by rw [(exists_pot B.host N).choose_spec γ L L' h]
  rhoDet_eq_inv_muTilde_chiD_pow _ _ _ := rfl
  rhoDetPrime_eq_muTilde_mul_chi_pow _ _ _ := rfl


open Classical in
def cols (B : Base) : Cols B where
  toCols0 := cols0 B.toPre
  fm u :=
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    { forms B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) B.LL B.embLL B.places with }

theorem two_lt_alt (u : B.Word) : 2 < B.T u := by
  have h := B.level_mod_four _ (B.T_level u)
  have h2 := (B.T_prime u).two_le
  omega


end Chain

end GlobalTheory.Mem.ColsModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure GJStage (B : Base) (C : Cols B) where
  vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W
  cd : CDHaar
  jet : ThetaJet B.R B.host
  jetU : jet.Sit → B.Word
  jetL : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i)
  jetW : jet.Sit → B.places.Pl
  jetW_l : ∀ i, B.places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → (Tau B.R)
  jetW1 : jet.Sit1 → B.places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, B.places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → (Tau B.R)
  jetU1 : jet.Sit1 → B.Word
  jetL1 : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i)
  gx : GlobalExtra B.LL (Tau B.R)
  gat : ∀ u (w : B.places.Pl), GIdx B.host (C.mem u).A.T (B.places.resChar w) →
    Formalism.MainNotions.G.GAtP (B.places.resChar w)
  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (C.mem u).A.Mu0

end GlobalTheory.Mem

end
end

