module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
section
namespace GlobalTheory

theorem exists_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    ∃ q : Y → ℕ, (∀ x y, q (x - y) ≤ q x + q y) ∧ (∀ (m : ℕ) y, q (m • y) = m * q y) ∧
      ∀ y, q y = 0 → y = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  refine ⟨fun y => ∑ i, (b.repr y i).natAbs, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub, Finsupp.sub_apply]
    exact Int.natAbs_sub_le _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    apply b.repr.injective
    ext i
    simpa using hy i (Finset.mem_univ i)

theorem exists_invariant_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) :
    ∃ p : Y → ℕ, (∀ x y, p (x - y) ≤ p x + p y) ∧ (∀ (m : ℕ) y, p (m • y) = m * p y) ∧
      (∀ y, p y = 0 → y = 0) ∧ ∀ y, p (σ y) = p y := by
  obtain ⟨q, h1, h2, h3⟩ := exists_nat_length_lattice Y
  refine ⟨fun y => ∑ j ∈ Finset.range n, q ((σ ^ j) y), ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub]
    exact h1 _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, h2]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    have := hy 0 (Finset.mem_range.mpr hn)
    exact h3 y (by simpa using this)
  · intro y
    have e1 := Finset.sum_range_succ (fun j => q ((σ ^ j) y)) n
    have e2 := Finset.sum_range_succ' (fun j => q ((σ ^ j) y)) n
    have e3 : ∑ j ∈ Finset.range n, q ((σ ^ j) (σ y)) =
        ∑ j ∈ Finset.range n, q ((σ ^ (j + 1)) y) :=
      Finset.sum_congr rfl fun j _ => by rw [pow_succ, Module.End.mul_apply]
    rw [hσ] at e1
    rw [pow_zero] at e2
    simp only [e3]
    omega

theorem end_eq_one_of_pow_eq_one_of_congr (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n M : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) (hM : 3 ≤ M)
    (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_invariant_nat_length_lattice Y σ n hn hσ
  have key : ∀ (k : ℕ) (y : Y), p y = k → σ y = y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      obtain ⟨z, hz⟩ := h y
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : y = 0 := h3 y (hy.trans hk)
        rw [this, map_zero]
      have hle : M * p z ≤ k + k := by
        have := h1 (σ y) y
        rw [h4, hy, hz, add_sub_cancel_left, h2] at this
        exact this
      have hlt : p z < k := by nlinarith
      have hzz : σ z = z := ih _ hlt z rfl
      have hj : ∀ j : ℕ, (σ ^ j) y = y + (j * M) • z := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', Module.End.mul_apply, ihj, map_add (f := _), map_nsmul, hzz, hz, add_mul, one_mul,
            add_smul]
          abel
      have h0 : (n * M) • z = 0 := by
        have := hj n
        rw [hσ, Module.End.one_apply] at this
        exact left_eq_add.mp this
      have h00 : p z = 0 := by
        have e := h2 (n * M) z
        have e0 := h2 0 z
        rw [zero_smul, zero_mul] at e0
        rw [h0, e0] at e
        have : 0 < n * M := Nat.mul_pos hn (by omega)
        rcases Nat.mul_eq_zero.mp e.symm with h' | h'
        · omega
        · exact h'
      rw [hz, h3 z h00, smul_zero, add_zero]
  ext y
  exact key _ y rfl

theorem latMinkowski : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatMinkowskiSt := by
  intro Y _ _ _ σ n M hn hσ hM h
  have hp : (σ : Module.End ℤ Y) ^ n = 1 := by
    ext y
    have : (σ ^ n) y = y := by rw [hσ]; rfl
    rw [LinearEquiv.pow_apply] at this
    rw [Module.End.pow_apply]
    exact this
  have := end_eq_one_of_pow_eq_one_of_congr Y (σ : Module.End ℤ Y) n M hn hp hM h
  ext y
  exact LinearMap.congr_fun this y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsoPullCancel
section
noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_iso_pull_cancel {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} (hL : L.IsLB)
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {φ₁ : X'' ⟶ X} {φ₂ : X' ⟶ X} {θ : X'' ⟶ X'} (h : θ ≫ φ₂ = φ₁)
    (w₁ : LB.Iso L'' (L.pull φ₁)) (w₂ : LB.Iso L' (L.pull φ₂)) (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ (wθ : LB.Iso L'' (L'.pull θ)) (w₁' : LB.Iso L'' (L.pull (θ ≫ φ₂))),
      wθ.IsGen ∧ HEq w₁' w₁ ∧ Tri w₂ wθ w₁' := by
  subst h
  obtain ⟨wθ, T⟩ := exists_cancel hL w₂ w₁ ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁) hL' hL''
  exact ⟨wθ, w₁, (isGen_iff _).2 (T.pgen_cancel hL ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁)), HEq.rfl, T⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOneOfPosDefForm
section
namespace GlobalTheory

theorem exists_pow_eq_one_of_posDef_form (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (b : LinearMap.BilinForm ℤ Y) (hs : ∀ y z, b y z = b z y) (hp : ∀ y, y ≠ 0 → 0 < b y y)
    (σ : Y ≃ₗ[ℤ] Y) (hσ : ∀ y z, b (σ y) (σ z) = b y z) : ∃ n : ℕ, 0 < n ∧ σ ^ n = 1 := by
  classical
  rw [← isOfFinOrder_iff_pow_eq_one]
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  let e := Module.Free.chooseBasis ℤ Y
  have h0 : ∀ y, 0 ≤ b y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have hpow : ∀ (n : ℕ) y, b ((σ ^ n) y) ((σ ^ n) y) = b y y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', LinearEquiv.mul_apply, hσ, ih]
  have hnd : ∀ y, (∀ j, b y (e j) = 0) → y = 0 := by
    intro y hy
    by_contra h
    have : b y = 0 := e.ext fun j => by simpa using hy j
    have h2 := hp y h
    simp [this] at h2
  let f : ℕ → (_ → _ → ℤ) := fun n i j => b ((σ ^ n) (e i)) (e j)
  have hf : Function.Injective f := by
    intro m n h
    apply hinj
    apply LinearEquiv.toLinearMap_injective
    refine e.ext fun i => ?_
    rw [← sub_eq_zero]
    apply hnd
    intro j
    have := congrFun (congrFun h i) j
    simp only [f] at this
    simp [this]
  let C : _ → _ → ℤ := fun i j => b (e i) (e i) * b (e j) (e j)
  have hS : (Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (-C i j) (C i j)).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => Set.finite_Icc _ _
  refine Set.infinite_of_injective_forall_mem hf (fun n => ?_) hS
  intro i _ j _
  have h1 := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le b h0 ((σ ^ n) (e i)) (e j)
  rw [hpow, hs (e j), hs (e j)] at h1
  have h2 : f n i j ^ 2 ≤ C i j := by
    simp only [f, C]; nlinarith [h1]
  constructor <;> nlinarith [h2, sq_nonneg (f n i j - 1), sq_nonneg (f n i j + 1), Int.le_self_sq (f n i j), Int.le_self_sq (-f n i j)]

theorem latFinOrdSt : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatFinOrdSt :=
  fun Y _ _ _ b hs hp σ hσ => exists_pow_eq_one_of_posDef_form Y b hs hp σ hσ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamFree

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FamSec (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

abbrev multiples (D : DegPre R) (k : ℕ) : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range

theorem zero_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s (α + k • mu)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k mu α
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem zero_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s β).f j = 0 := by
  obtain ⟨mu, rfl⟩ := hβ
  exact zero_add_nsmul hG s α mu h

theorem zero_add_nsmul_iff (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X) :
    (∀ j, (s.s (α + k • mu)).f j = 0) ↔ ∀ j, (s.s α).f j = 0 :=
  ⟨zero_of_eq_add_nsmul hG s ⟨-mu, by rw [smul_neg, add_neg_cancel_right]⟩, zero_add_nsmul hG s α mu⟩

theorem eq_of_eq_add_nsmul (hG : GlobalFnsSt) {k : ℕ} (s t : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : s.s α = t.s α) : s.s β = t.s β := by
  have h0 := zero_of_eq_add_nsmul hG (s + -t) hβ (fun j => by rw [add_f, neg_f, h, add_neg_cancel])
  refine SecOps.sec_ext fun j => ?_
  have := h0 j
  rw [add_f, neg_f, add_neg_eq_zero] at this
  exact this

theorem add_nsmul_inj {k : ℕ} (hk : 1 ≤ k) (ρ a b : D.X) (h : ρ + k • a = ρ + k • b) : a = b := by
  have h' : (k : ℤ) • a = (k : ℤ) • b := by
    rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
  exact smul_right_injective D.X (by omega : (k : ℤ) ≠ 0) h'

theorem exists_fam_single (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (ρ : D.X)
    (σ : FamSec D F k ρ) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 :=
  UUA.exists_fam_rep hG hB k ρ (add_nsmul_inj hk ρ) σ

theorem existsUnique_fam_of_reps (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) {C : Type*}
    (rep : C → D.X) (hrep : ∀ α : D.X, ∃! c, ∃ mu, rep c + k • mu = α) (σ : ∀ c, FamSec D F k (rep c)) :
    ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c := by
  choose cl hcl hcl' using hrep
  choose f hf _ using fun c => exists_fam_single hG hB hk (rep c) (σ c)
  have key : ∀ (α β : D.X) (c : C), cl β = c → (f (cl β)).s β = (f c).s β := by
    rintro α β c rfl; rfl
  refine ⟨⟨fun β => (f (cl β)).s β, fun mu α u hu hc => ?_⟩, fun c => ?_, fun s hs => ?_⟩
  · have e : cl (α + k • mu) = cl α := by
      obtain ⟨nu, hnu⟩ := hcl α
      exact (hcl' (α + k • mu) (cl α) ⟨nu + mu, by rw [smul_add, ← add_assoc, hnu]⟩).symm
    have := (f (cl α)).fe mu α u hu hc
    rw [← key α _ _ e] at this
    exact this
  · have e : cl (rep c) = c := (hcl' (rep c) c ⟨0, by rw [smul_zero, add_zero]⟩).symm
    exact (key (rep c) _ _ e).trans (hf c)
  · refine fam_ext fun α j => ?_
    have := eq_of_eq_add_nsmul hG s (f (cl α)) (hcl α) ((hs (cl α)).trans (hf (cl α)).symm)
    rw [this]

theorem mk_eq_mk_iff {k : ℕ} (α β : D.X) :
    (QuotientAddGroup.mk α : D.X ⧸ multiples D k) = QuotientAddGroup.mk β ↔ ∃ mu, α + k • mu = β := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨mu, h⟩
    exact ⟨mu, by rw [show k • mu = -α + β from h, add_neg_cancel_left]⟩
  · rintro ⟨mu, rfl⟩
    exact ⟨mu, by rw [neg_add_cancel_left]; rfl⟩

theorem existsUnique_fam (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k)
    (rep : D.X ⧸ multiples D k → D.X) (hrep : ∀ c, QuotientAddGroup.mk (rep c) = c)
    (σ : ∀ c, FamSec D F k (rep c)) : ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c :=
  existsUnique_fam_of_reps hG hB hk rep (fun α => ⟨QuotientAddGroup.mk α, (mk_eq_mk_iff _ _).1 (hrep _),
    fun c hc => (hrep c).symm.trans ((mk_eq_mk_iff _ _).2 hc)⟩) σ

theorem IsSecBasis.ne_zero {S : Scheme.{0}} {A T : Over S} [Nontrivial Γ(T.left, ⊤)] {N : LB (T ⊗ A).left} {m : ℕ}
    {b : Fin m → LB.Sec N} (hb : IsSecBasis N b) (i : Fin m) : ¬ ∀ j, (b i).f j = 0 := by
  classical
  intro h
  obtain ⟨r, -, hr⟩ := hb SecOps.secZero
  have h0 := hr 0 (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    simp only [Pi.zero_apply, map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero])
  have h1 := hr (Pi.single i 1) (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    refine (Finset.sum_eq_zero fun i' _ => ?_).symm
    by_cases e : i' = i
    · rw [e, h j, mul_zero]
    · rw [Pi.single_eq_of_ne e, map_zero, map_zero, MulZeroClass.zero_mul])
  have := congrFun (h1.trans h0.symm) i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

theorem exists_sec_ne_zero (hT : SecTwistSt) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ σ : FamSec D F k α, ¬ ∀ j, σ.f j = 0 := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk F (jFK (R := R) F ≫ jK R) (cP D (TF (R := R) F) α)
  have : Nontrivial Γ((TF (R := R) F).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := IsSecBasis.ne_zero hb ⟨0, pow_pos (by omega) _⟩
  let q : (DegPre.BF D F).left ⟶ (TK R).left := (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F
  let u := LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi α) D.rigK) q
  have hu : u.IsGen := pullGen_isGen _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen α) (pullGen_isGen _ _ _ _ D.rig_gen _)) _
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F α) (ε' := DegPre.famε k) (fun U _ h => by
      have p := prod_fam D F (𝟙 _) α k h
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₁ : q ≫ D.xK α = (cP D (DegPre.BF D F) α).left :=
        congrArg (fun x => x.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have a₂ : q ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun x : DegPre.BF D F ⟶ D.P.A => x.left)
          (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have a₃ : translPt D.P.A (cP D (TF (R := R) F) α) = cP D (DegPre.BF D F) α * DegPre.prB D F := by
        rw [translPt, comp_cP]; rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Category.id_comp, a₁, a₂, a₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one]
      rw [← _root_.mul_assoc])
    (pullMulSec (b ⟨0, pow_pos (by omega) _⟩) (𝟙 _) u hu)
  refine ⟨σ, fun h => hne fun j => ?_⟩
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := (hσ _ (𝟙 _) y J hJ).trans (sval_pullMulSec _ _ _ hu _ y hJ)
  rw [UUA.sval_zero_of h _ y J (hJ.mem _ _), Category.id_comp] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem exists_fam_support (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ s : Fam D F k, ∀ β : D.X, (¬ ∀ j, (s.s β).f j = 0) ↔ ∃ mu, α + k • mu = β := by
  obtain ⟨σ, hσ⟩ := exists_sec_ne_zero (D := D) (F := F) hT hk α
  obtain ⟨s, rfl, hs⟩ := exists_fam_single hG hB hk α σ
  refine ⟨s, fun β => ⟨fun h => by_contra fun hn => h (hs β fun mu e => hn ⟨mu, e⟩), ?_⟩⟩
  rintro ⟨mu, rfl⟩ h
  exact hσ ((zero_add_nsmul_iff hG s α mu).1 h)

end GlobalTheory.FamFree

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullTopZFConstUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

section Sections

variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]

def secVal {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε)) : Γ(Y, ⊤) :=
  (Y.presheaf.map (homOfLE (wchart_triv φ (fun _ => PUnit.unit)).ge).op).hom (s.f (fun _ => PUnit.unit))

theorem map_self {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)) : (Y.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem sec_f_eq {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε))
    (j : J → (Inh.trivLB Z).ι) :
    s.f j = (Y.presheaf.map (homOfLE le_top).op).hom (secVal s) := by
  obtain rfl : j = fun _ => PUnit.unit := rfl
  exact ((map_map _ _ _).trans (map_self _ _)).symm

theorem map_top_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)}
    (h : (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = (Y.presheaf.map (homOfLE le_top).op).hom b) :
    a = b := by
  subst hV
  rwa [map_self, map_self] at h

theorem secVal_of_secRel {φ₁ : J₁ → (Y ⟶ Z)} {ε₁ : J₁ → ℤ} {s₁ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₁ ε₁)}
    {φ₂ : J₂ → (Y ⟶ Z)} {ε₂ : J₂ → ℤ} {s₂ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₂ ε₂)} {h : Y ⟶ Y}
    (hh : h = 𝟙 Y) {φ₃ : J₃ → (Y ⟶ Z)} {ε₃ : J₃ → ℤ} {u : LB.Gen (LB.LinComb (Inh.trivLB Z) φ₃ ε₃)}
    {a : Γ(Y, ⊤)ˣ} (hu : IsConst u a)
    (H : GeneratorPullback.SecRel (Inh.trivLB Z) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u) : secVal s₁ = secVal s₂ * a := by
  have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
  subst hh
  refine map_top_inj (top_unique (le_inf (le_inf (wchart_triv φ₁ _).ge (wchart_triv _ _).ge)
    (wchart_triv φ₃ _).ge)) (Eq.trans ?_ (this.trans ?_))
  · exact (map_map _ _ _).symm.trans (congrArg _ (sec_f_eq s₁ _).symm)
  · rw [map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (congrArg _ (congrArg _ (sec_f_eq s₂ _))).trans (app_res _ _ _ _ _)
    · exact (congrArg _ (congrArg Units.val (hu _))).trans (map_map _ _ _)

end Sections

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]

theorem trPt_eq_id (b : TF (R := K) F ⟶ (toricPre K X q).P.A) :
    DegPre.trPt (toricPre K X q) F b = 𝟙 _ :=
  CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)

def constUnit : Fˣ →* Γ((DegPre.BF (toricPre K X q) F).left, ⊤)ˣ :=
  (pullTop (fst (TF (R := K) F) (toricPre K X q).P.A).left).comp
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom)

theorem pullTop_zF_constUnit (c : Fˣ) :
    pullTop (DegPre.zF (toricPre K X q) F).left (constUnit q F c) = unitOn c := by
  have h : (DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]
  ext
  change ((DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left).appTop.hom
    (unitOn c).val = _
  rw [h]
  rfl

theorem secVal_of_phiRel {n : ℕ} (p : QkPt (toricPre K X q) F n) (t : Multiplicative X →* Fˣ)
    (hp : p.g = pt q F t)
    (w : LB.Gen (LB.LinComb (toricPre K X q).P.L (DegPre.lineφ _ F p.g.b) (DegPre.lineε n))) (c : Fˣ)
    (hw : IsConst w (unitOn c)) {s s' : Fam (toricPre K X q) F n} (h : PhiRel _ F n p w s s') (α β : X)
    (hβ : β = α + (show X from p.y)) :
    secVal (s'.s β) = secVal (s.s α) * (constUnit q F (t (Multiplicative.ofAdd α) * c)).val := by
  subst hβ
  have hg : IsConst (p.g.s α) (unitOn (t (Multiplicative.ofAdd α))) := by
    rw [hp]
    exact pt_isConst q F t α
  refine secVal_of_secRel (congrArg CommaMorphism.left (trPt_eq_id q F p.g.b)) (cg_isConst _ _ _)
    (h α (cg _ _ (constUnit q F (t (Multiplicative.ofAdd α) * c))) (cg_isGen _ _ _) ?_)
  exact corr_of_isConst
    ((isConst_pullGen (cg_isConst _ _ _) _).of_eq ((pullTop_zF_constUnit q F _).trans (unitOn_mul _ _)))
    (isConst_mulGen hg hw)

theorem weilQkIs_pt {n : ℕ} (p p' : QkPt (toricPre K X q) F n) (t t') (hp : p.g = pt q F t) (hp' : p'.g = pt q F t') :
    WeilQkIs (toricPre K X q) F n p p'
      ((t (Multiplicative.ofAdd (show X from p'.y)) * (t' (Multiplicative.ofAdd (show X from p.y)))⁻¹ : Fˣ) : F) := by
  intro w w' _ _ s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ β j
  obtain ⟨a, ha⟩ := exists_isConst w
  obtain ⟨c, rfl⟩ := unitOn_bijective.2 a
  obtain ⟨a', ha'⟩ := exists_isConst w'
  obtain ⟨c', rfl⟩ := unitOn_bijective.2 a'
  change X at β
  let y : X := p.y
  let y' : X := p'.y
  have e₁ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₁ (β - y - y') (β - y - y' + y') rfl
  have e₂ := secVal_of_phiRel q F p t hp w c ha h₂ (β - y - y' + y') β (show β = β - y - y' + y' + y by abel)
  have e₃ := secVal_of_phiRel q F p t hp w c ha h₃ (β - y - y') (β - y - y' + y) rfl
  have e₄ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₄ (β - y - y' + y) β (show β = β - y - y' + y + y' by abel)
  have e : secVal (s₂.s β) = (constUnit q F (t (Multiplicative.ofAdd y') * (t' (Multiplicative.ofAdd y))⁻¹)).val *
      secVal (s₄.s β) := by
    rw [e₂, e₄, e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, mul_left_comm (Units.val _), ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 3
    simp only [ofAdd_add, map_mul]
    generalize t (Multiplicative.ofAdd (β - y - y')) = A
    generalize t' (Multiplicative.ofAdd (β - y - y')) = B
    generalize t (Multiplicative.ofAdd y') = C
    generalize t' (Multiplicative.ofAdd y) = D
    ext
    push_cast
    field_simp
  refine (sec_f_eq (s₂.s β) j).trans ?_
  rw [e, map_mul, sec_f_eq (s₄.s β) j]
  rfl

end GlobalTheory.ToricData
end
end

