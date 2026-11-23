module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.Bundle0009
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cur (M : TRep R G) (x : M.coch.X 2) (g h : G) : M.V := x.1 ![g, h]

theorem cur_sub (M : TRep R G) (x x' : M.coch.X 2) (g h : G) :
    cur M (x - x') g h = cur M x g h - cur M x' g h := rfl

theorem isTwoCocycle_curried (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) : IsTwoCocycle M.rho (cur M x) := by
  intro g h k
  have := congrFun (LowDeg.dn_eq_zero M hx) ![g, h, k]
  rw [LowDeg.dn_two_apply] at this
  exact this

theorem ext2 (M : TRep R G) {x x' : M.coch.X 2} (h : ∀ g h, cur M x g h = cur M x' g h) : x = x' := by
  refine Subtype.ext (funext fun v => ?_)
  have hv : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [hv]; exact h _ _

theorem continuous_cur (M : TRep R G) (x : M.coch.X 2) {X : Type*} [TopologicalSpace X] {f h : X → G}
    (hf : Continuous f) (hh : Continuous h) : Continuous fun t => cur M x (f t) (h t) := by
  refine (show Continuous x.1 from x.2).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact hf
  · exact hh

def mk1 (M : TRep R G) (y : G → M.V) (hy : Continuous y) : M.coch.X 1 :=
  ⟨fun v => y (v 0), hy.comp (continuous_apply 0)⟩

theorem curried_coboundary_eq (M : TRep R G) (y : G → M.V) (hy : Continuous y) (g h : G) :
    cur M (M.coch.d 1 (mk1 M y hy)) g h = D1 M.rho y g h := oneDifferential_val M _ g h

theorem d_sub_d (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) (w : M.coch.X 1) :
    M.coch.d 2 (x - M.coch.d 1 w) = 0 := by
  rw [map_sub, hx, M.coch.dd, sub_zero]

theorem continuous_comp_rep (U : Subgroup G) (hU : IsOpen (U : Set G)) {Y : Type*} [TopologicalSpace Y]
    (e : G → Y) : Continuous fun g => e (rep U g) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x := by
    refine (hU.preimage (continuous_mul_const _)).mem_nhds ?_
    simp [U.one_mem]
  refine (continuousAt_const (y := e (rep U x))).congr ?_
  filter_upwards [hn] with y hy
  have : y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x := by simp
  rw [this, rep_mul]

variable (M : TRep R G) (N : Subgroup G)

theorem retr_mul_rep (g : G) : (retr N g : G) * rep N g = g := by simp [retr_spec]

theorem retr_mul' (n : G) (hn : n ∈ N) (g : G) : (retr N (n * g) : G) = n * retr N g :=
  congrArg Subtype.val (retr_mul N ⟨n, hn⟩ g)

theorem rep_mul' (n : G) (hn : n ∈ N) (g : G) : rep N (n * g) = rep N g := rep_mul N ⟨n, hn⟩ g

theorem continuous_retr' (hN : IsOpen (N : Set G)) : Continuous fun g => (retr N g : G) :=
  continuous_subtype_val.comp (continuous_retr N hN)

theorem norm0 (hN : IsOpen (N : Set G)) (x : M.coch.X 2)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ m ∈ N, cur M (x - M.coch.d 1 w) n m = 0 := by
  obtain ⟨y, hy⟩ := (memB _).1 hres
  have hc : Continuous fun g : G => (y.1 (e1 (retr N g * (retr N 1)⁻¹)) : M.V) :=
    (show Continuous y.1 from y.2).comp
      (continuous_pi fun _ => (continuous_retr N hN).mul continuous_const)
  have hval : ∀ n : N, retr N (n : G) * (retr N 1)⁻¹ = n := fun n => by
    have := retr_mul N n 1
    rw [mul_one] at this
    rw [this, mul_inv_cancel_right]
  obtain ⟨Y, hYc, hYv⟩ : ∃ Y : G → M.V, Continuous Y ∧ ∀ n : N, Y n = y.1 (e1 n) :=
    ⟨fun g => y.1 (e1 (retr N g * (retr N 1)⁻¹)), hc, fun n => by
      show y.1 (e1 (retr N (n : G) * (retr N 1)⁻¹)) = _
      rw [hval]⟩
  refine ⟨mk1 M Y hYc, fun n hn m hm => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  have h1 := oneDifferential_val (M.resSub N) y ⟨n, hn⟩ ⟨m, hm⟩
  rw [hy] at h1
  have h2 : ((Pair.res M N.subtype continuous_subtype_val).hom.f 2 x).1 ![⟨n, hn⟩, ⟨m, hm⟩] = cur M x n m := by
    refine congrArg x.1 (funext fun i => ?_)
    fin_cases i <;> rfl
  rw [h2] at h1
  rw [h1]
  simp only [D1]
  have e1' : Y n = y.1 (e1 ⟨n, hn⟩) := hYv ⟨n, hn⟩
  have e2' : Y m = y.1 (e1 ⟨m, hm⟩) := hYv ⟨m, hm⟩
  have e3' : Y (n * m) = y.1 (e1 (⟨n, hn⟩ * ⟨m, hm⟩)) := hYv (⟨n, hn⟩ * ⟨m, hm⟩)
  rw [e1', e2', e3']
  exact sub_self _

theorem normA (hN : IsOpen (N : Set G)) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ m ∈ N, cur M x n m = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 := by
  have hc : Continuous fun g : G => - cur M x (retr N g) (rep N g) :=
    (continuous_cur M x (continuous_retr' N hN) (continuous_rep N hN)).neg
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  exact stepA (isTwoCocycle_curried M x hx) (retr_mul_rep N)
    (fun g => (retr N g).property) (retr_mul' N) (rep_mul' N) h0 n hn g

theorem normB [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0) (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  have hC := isTwoCocycle_curried M x hx
  have hex : ∀ g : G, ∃ e : M.V, (g ∈ N → e = 0) ∧
      ∀ n ∈ N, cur M x g (g⁻¹ * n * g) = e - M.rho n e := by
    intro g
    by_cases hg : g ∈ N
    · exact ⟨0, fun _ => rfl, fun n _ => by rw [h0 g hg, map_zero, sub_zero]⟩
    · let θ : (M.resSub N).coch.X 1 := ⟨fun v => cur M x g (g⁻¹ * (v 0 : G) * g),
        continuous_cur M x continuous_const
          ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))).mul continuous_const)⟩
      have hθ : (M.resSub N).coch.d 1 θ = 0 := by
        rw [wach_d1_eq_zero_iff]
        intro a b
        show cur M x g (g⁻¹ * ((a * b : N) : G) * g) =
          cur M x g (g⁻¹ * (a : G) * g) + M.rho (a : G) (cur M x g (g⁻¹ * (b : G) * g))
        have e1 : g⁻¹ * ((a * b : N) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) := by
          rw [Subgroup.coe_mul]; group
        rw [e1, theta_mul hC h0 g _ (Subgroup.Normal.conj_mem' ‹_› _ a.2 g)]
        congr 3
        group
      have hz : (Submodule.Quotient.mk ⟨θ, (memZ _).2 hθ⟩ : (M.resSub N).H 1) = 0 := Subsingleton.elim _ _
      rw [mk_eq_zero_iff, mem_oneCoboundaries_iff] at hz
      obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ a : N, cur M x g (g⁻¹ * (a : G) * g) = M.rho (a : G) m - m := hz
      refine ⟨-m, fun h => absurd h hg, fun n hn => ?_⟩
      have h' : cur M x g (g⁻¹ * n * g) = M.rho n m - m := hm ⟨n, hn⟩
      rw [h', map_neg]; abel
  choose e he0 he using hex
  have hc : Continuous fun g : G => M.rho (retr N g : G) (e (rep N g)) :=
    M.cont.comp (f := fun g : G => ((retr N g : G), e (rep N g)))
      ((continuous_retr' N hN).prodMk (continuous_comp_rep N hN e))
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq, cur_sub, curried_coboundary_eq]
  exact stepB hC (retr_mul_rep N) (fun g => (retr N g).property)
    (retr_mul' N) (rep_mul' N) h0 e he0 he n hn g

theorem norm_all [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  obtain ⟨w0, h0⟩ := norm0 M N hN x hres
  obtain ⟨w1, hA⟩ := normA M N hN _ (d_sub_d M x hx w0) h0
  obtain ⟨w2, hB⟩ := normB M N hN h1 _ (d_sub_d M _ (d_sub_d M x hx w0) w1) hA
  refine ⟨w0 + w1 + w2, ?_⟩
  have : x - M.coch.d 1 (w0 + w1 + w2) = x - M.coch.d 1 w0 - M.coch.d 1 w1 - M.coch.d 1 w2 := by
    rw [map_add (f := _), map_add (f := _)]; abel
  rw [this]
  exact hB

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer

open _root_.Neutral.B1

noncomputable section

def quotAddCongr {R R' A A' : Type} [Ring R] [Ring R'] [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R' A']
    (P : Submodule R A) (P' : Submodule R' A') (e : A ≃+ A') (h : ∀ x, x ∈ P ↔ e x ∈ P') : (A ⧸ P) ≃+ (A' ⧸ P') :=
  QuotientAddGroup.congr P.toAddSubgroup P'.toAddSubgroup e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩)

section Scalars

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation ℤ G M) (h : ∀ g m, rho g m = rho' g m)

def oneCocyclesScalarEquiv : Z1 rho ≃+ Z1 rho' where
  toFun f := ⟨f.1, f.2.1, fun g k => by rw [← h]; exact f.2.2 g k⟩
  invFun f := ⟨f.1, f.2.1, fun g k => by rw [h]; exact f.2.2 g k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def h1ScalarEquiv : H1 rho ≃+ H1 rho' :=
  quotAddCongr _ _ (oneCocyclesScalarEquiv rho rho' h) fun f => by
    show f.1 ∈ Bd1 rho ↔ f.1 ∈ Bd1 rho'
    simp only [mem_contCoboundaries1, h]

end Scalars

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem kbarRep_apply (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := rfl

theorem contAction_kbarRep : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro x
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun σ₀ => ?_)
  have hx := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  refine ⟨_, hx.preimage (continuous_const_mul σ₀⁻¹), ?_, ?_⟩
  · simp
  · intro σ hσ
    have h1 : (σ₀⁻¹ * σ) ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) := hσ
    have h2 : σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ₀ (Additive.toMul x : (PadicAlgCl p)ˣ) := by
      have := congrArg σ₀ h1
      simpa [AlgEquiv.mul_apply] using this
    exact Units.ext h2

def kT : ReciprocityTheory.Coh.TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := contAction_kbarRep p K

def muRep : Representation ℤ (GK p K) (ZMod n) where
  toFun g := (charRep (cycK p K n) g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by
    show charRep (cycK p K n) 1 x = x
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    show charRep (cycK p K n) (g * h) x = charRep (cycK p K n) g (charRep (cycK p K n) h x)
    rw [map_mul]; rfl

theorem muRep_apply (g : GK p K) (x : ZMod n) : muRep p K n g x = ((cycK p K n g : (ZMod n)ˣ) : ZMod n) * x := rfl

variable {p n}

def muMap (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) : ZMod n →ₗ[ℤ] KbarMult p :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun k => (Additive.ofMul (ζ ^ k.val) : KbarMult p)
      map_zero' := by simp; rfl
      map_add' := fun a b => by
        show ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val
        rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add] }

theorem muMap_apply (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (k : ZMod n) :
    muMap ζ hζ k = (Additive.ofMul (ζ ^ k.val) : KbarMult p) := rfl

theorem muMap_equiv (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (g : GK p K) (k : ZMod n) :
    muMap ζ hζ (muRep p K n g k) = kbarRep p K g (muMap ζ hζ k) := by
  rw [muMap_apply, muMap_apply, kbarRep_apply, muRep_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  have h1 : ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Units.val_one]
  have h2 := cycN_spec (K := K) (L := PadicAlgCl p) (n := n) g _ h1
  show _ = g ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  rw [h2, ← Units.val_pow_eq_pow_val, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, ← pow_mul, mul_comm]

theorem muMap_injective {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (muMap ζ hζ.pow_eq_one) := by
  intro a b hab
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)


variable (p n) in
def powMap : KbarMult p →ₗ[ℤ] KbarMult p := (n : ℤ) • LinearMap.id

theorem powMap_apply (x : (PadicAlgCl p)ˣ) :
    powMap p n (Additive.ofMul x : KbarMult p) = (Additive.ofMul (x ^ n) : KbarMult p) := by
  show (n : ℤ) • (Additive.ofMul x : Additive (PadicAlgCl p)ˣ) = _
  rw [natCast_zsmul]; rfl

theorem powMap_surjective : Function.Surjective (powMap p n) := by
  intro y
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hz
    exact (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : KbarMult p), ?_⟩
  rw [powMap_apply]
  exact congrArg Additive.ofMul (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz))

theorem exact_muMap_powMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by
  intro y
  constructor
  · intro hy
    have h1 : (Additive.toMul y : (PadicAlgCl p)ˣ) ^ n = 1 := by
      have := powMap_apply (p := p) (n := n) (Additive.toMul y)
      exact (this.symm.trans hy : _)
    have h2 : ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one h2
    have hi'' : ζ ^ i = (Additive.toMul y : (PadicAlgCl p)ˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi')
    refine ⟨(i : ZMod n), ?_⟩
    rw [muMap_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi'']; rfl
  · rintro ⟨k, rfl⟩
    rw [muMap_apply, powMap_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]; rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev GKab : Type := TopologicalAbelianization (GK p K)

def toAbK : GK p K →* GKab p K := QuotientGroup.mk' _

structure IsAbLK : Prop where
  le : K ≤ L
  fin : FiniteDimensional ℚ_[p] L
  comm : commutator (GK p K) ≤ subG p K L

def normHom : KbarMult p →+ KbarMult p :=
  ∑ᶠ c : GK p K ⧸ subG p K L, (kbarRep p K c.out).toAddMonoidHom

def normSub : AddSubgroup (KbarMult p) := (multOf p L).map (normHom p K L)

def normGrp : Subgroup Kˣ := AddSubgroup.toSubgroup' ((normSub p K L).comap (ofK p K))

theorem mem_normGrp_iff (x : Kˣ) :
    x ∈ normGrp p K L ↔ ∃ y ∈ multOf p L, normHom p K L y = ofK p K (Additive.ofMul x) := Iff.rfl

def IsArtinK (Art : Kˣ →* GKab p K) : Prop :=
  Continuous Art ∧ Function.Injective Art ∧ DenseRange Art ∧
  (∀ π : Kˣ, vK p K π = 1 → ∀ g : GK p K, toAbK p K g = Art π → IsFrob p K g) ∧
  ∀ L, IsAbLK p K L →
    (∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧ g'⁻¹ * g ∈ subG p K L) ∧
    ∀ (x : Kˣ) (g : GK p K), toAbK p K g = Art x → (g ∈ subG p K L ↔ x ∈ normGrp p K L)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtE
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_closest {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (x : PadicAlgCl p) :
    ∃ m0 ∈ M, ∀ m ∈ M, ‖x - m0‖ ≤ ‖x - m‖ := by
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  have hc : IsCompact (Metric.closedBall (0 : M) ‖x‖) := isCompact_closedBall 0 ‖x‖
  have hcont : Continuous (fun m : M => ‖x - (m : PadicAlgCl p)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  have hne : (Metric.closedBall (0 : M) ‖x‖).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
  obtain ⟨m0, hm0, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hmin' : ∀ m : M, m ∈ Metric.closedBall (0 : M) ‖x‖ →
      ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x - (m : PadicAlgCl p)‖ := fun m hm => hmin hm
  have hle0 : ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x‖ := by
    have h2 := hmin' 0 (Metric.mem_closedBall_self (norm_nonneg x))
    rwa [ZeroMemClass.coe_zero, sub_zero] at h2
  refine ⟨m0, m0.2, fun m hm => ?_⟩
  by_cases hmx : ‖m‖ ≤ ‖x‖
  · exact hmin' ⟨m, hm⟩ (by rw [mem_closedBall_zero_iff]; exact hmx)
  · rw [not_le] at hmx
    refine hle0.trans ?_
    by_contra hlt
    rw [not_le] at hlt
    have e : m = x - (x - m) := by ring
    have h3 : ‖m‖ ≤ max ‖x‖ ‖x - m‖ := by
      conv_lhs => rw [e]
      exact UnramifiedExtensions.norm_sub_le_max' _ _
    exact absurd (h3.trans (max_le le_rfl hlt.le)) (not_le.2 hmx)

theorem le_of_resK_le_of_norm {M L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (hML : M ≤ L) (hres : resK p L ≤ resK p M)
    (h : ∀ x ∈ L, ∃ y ∈ M, ‖x‖ = ‖y‖) : L ≤ M := by
  intro x hx
  obtain ⟨m0, hm0, hmin⟩ := exists_closest p hM x
  by_contra hxM
  have hy0 : x - m0 ≠ 0 := fun h0 => hxM (by rw [sub_eq_zero.1 h0]; exact hm0)
  have hyL : x - m0 ∈ L := L.sub_mem hx (hML hm0)
  obtain ⟨k, hk, hyk⟩ := h _ hyL
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hyk
    exact hy0 hyk
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  have h1 : ‖(x - m0) / k‖ = 1 := by rw [norm_div, hyk, div_self hkn.ne']
  have hmem : IsLocalRing.residue (Obar p) ⟨(x - m0) / k, mem_Obar_iff.2 h1.le⟩ ∈ resK p L :=
    (mem_resK_iff p L _).2 ⟨_, L.div_mem hyL (hML hk), rfl⟩
  obtain ⟨z, hz, hzr⟩ := (mem_resK_iff p M _).1 (hres hmem)
  rw [residue_eq_iff] at hzr
  have hzr' : ‖(z : PadicAlgCl p) - (x - m0) / k‖ < 1 := hzr
  have hlt : ‖x - (m0 + k * (z : PadicAlgCl p))‖ < ‖x - m0‖ := by
    have e : x - (m0 + k * (z : PadicAlgCl p)) = -(k * ((z : PadicAlgCl p) - (x - m0) / k)) := by
      rw [mul_sub, mul_div_cancel₀ _ hk0]
      ring
    rw [e, norm_neg, norm_mul, hyk]
    calc ‖k‖ * ‖(z : PadicAlgCl p) - (x - m0) / k‖ < ‖k‖ * 1 :=
          mul_lt_mul_of_pos_left hzr' hkn
      _ = ‖k‖ := mul_one _
  exact absurd hlt (not_lt.2 (hmin _ (M.add_mem hm0 (M.mul_mem hk hz))))

theorem eq_Kn_of_norm (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank ℚ_[p] L = n * Module.finrank ℚ_[p] K)
    (h : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : L = Kn p K n := by
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have hL : FiniteDimensional ℚ_[p] L :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.mul_pos hn hd)
  obtain ⟨f, hf, hq, -⟩ := qK_le_pow_finrank p K hK hL hKL
  have hM : FiniteDimensional ℚ_[p] (Kn p K f) := finiteDimensional_Kn p K hK hf
  have hML : Kn p K f ≤ L := Kn_le_of_qK p K hK hL hKL (n := f) (m := 1) (by rw [mul_one]; exact hq)
  have hres : resK p L ≤ resK p (Kn p K f) := by
    have hfin : Finite (resK p L) := finite_resK p L hL
    have hsub : (resK p (Kn p K f) : Set (kbar p)) ⊆ (resK p L : Set (kbar p)) := resK_mono p hML
    have hcard : (resK p L : Set (kbar p)).ncard ≤ (resK p (Kn p K f) : Set (kbar p)).ncard := by
      have e1 : (resK p L : Set (kbar p)).ncard = qK p L := (Nat.card_coe_set_eq _).symm
      have e2 : (resK p (Kn p K f) : Set (kbar p)).ncard = qK p (Kn p K f) :=
        (Nat.card_coe_set_eq _).symm
      rw [e1, e2, hq, qK_Kn p K hK hf]
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro c hc
    have : c ∈ (resK p (Kn p K f) : Set (kbar p)) := by rw [heq]; exact hc
    exact this
  have hLM : L = Kn p K f :=
    le_antisymm (le_of_resK_le_of_norm p hM hML hres
      (fun x hx => by
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact ⟨y, le_Kn p K f hy, hxy⟩)) hML
  have hfn : f = n := by
    have h1 := finrank_Kn p K hK hf
    rw [← hLM, hdeg] at h1
    exact (Nat.eq_of_mul_eq_mul_right hd h1).symm
  rw [hLM, hfn]

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

