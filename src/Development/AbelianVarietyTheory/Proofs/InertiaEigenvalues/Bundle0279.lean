module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTwCoef
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.TopSteps.CharAllCoef

section General

variable {O G : Type} [CommRing O] [Group G] [TopologicalSpace G]

theorem exists_mapH1_eq {M' M M'' : Type} [AddCommGroup M'] [Module O M'] [AddCommGroup M] [Module O M]
    [AddCommGroup M''] [Module O M''] {π' : Representation O G M'} {π : Representation O G M}
    {π'' : Representation O G M''} (f : M' →ₗ[O] M) (hf : ∀ g m, f (π' g m) = π g (f m))
    (q : M →ₗ[O] M'') (hq : ∀ g m, q (π g m) = π'' g (q m)) (hfi : Function.Injective f)
    (hqs : Function.Surjective q) (hex : Function.Exact f q)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (c : H1 π ⊤) (hc : mapH1 q hq c = 0) :
    ∃ c₀ : H1 π' ⊤, mapH1 f hf c₀ = c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b'', -, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨b, rfl⟩ := hqs b''
  have hb' : ∀ g, π'' g (q b) - q b = q ((z : G → M) g) := fun g => congrFun hb g
  have hr : ∀ g, ∃ y, f y = (z : G → M) g - (π g b - b) := fun g =>
    (hex _).mp (by rw [map_sub, map_sub, hq, hb', sub_self])
  choose w hw using hr
  have hwlc : IsLocallyConstant w := by
    have h1 : IsLocallyConstant fun g => (z : G → M) g - (π g b - b) :=
      z.2.1.1.sub ((hlc b).sub (IsLocallyConstant.const b))
    refine IsLocallyConstant.desc w f ?_ hfi
    have : f ∘ w = fun g => (z : G → M) g - (π g b - b) := funext hw
    rw [this]; exact h1
  refine ⟨Submodule.Quotient.mk ⟨w, ⟨hwlc, fun _ => Submodule.mem_top⟩, ?_⟩, ?_⟩
  · funext x
    change π' x.1 (w x.2) - w (x.1 * x.2) + w x.1 = 0
    apply hfi
    rw [map_add (f := _), map_sub, hf, hw, hw, hw, cocycle_mul, map_zero, map_mul]
    simp only [map_sub, Module.End.mul_apply]
    abel
  · refine (Submodule.Quotient.eq _).mpr ⟨-b, Submodule.mem_top, ?_⟩
    funext g
    change π g (-b) - -b = f (w g) - (z : G → M) g
    rw [hw, map_neg]
    abel

theorem exists_res_inj [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] [Nontrivial X] :
    ∃ f : (O ⧸ Ideal.span {lam}) →ₗ[O] X, Function.Injective f ∧ f ≠ 0 := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {lam} := hl.maximalIdeal_eq
  obtain ⟨x, hx0, hx⟩ : ∃ x : X, x ≠ 0 ∧ lam • x = 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun x : X => lam • x) := by
      intro a b hab
      by_contra hne
      exact h (a - b) (sub_ne_zero.mpr hne) (by rw [smul_sub]; exact sub_eq_zero.mpr hab)
    have hsurj := Finite.surjective_of_injective hinj
    have : (⊤ : Submodule O X) = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) ⊤ Module.Finite.fg_top ?_ ?_
      · intro y _
        obtain ⟨y', rfl⟩ := hsurj y
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
      · rw [← hmax, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact top_ne_bot this
  refine ⟨Submodule.liftQ (Ideal.span {lam}) (LinearMap.toSpanSingleton O X x) ?_, ?_, ?_⟩
  · rw [Ideal.span, Submodule.span_le]
    rintro _ rfl
    exact hx
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' : y • x = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [← hmax]
    intro hu
    exact hx0 (hu.smul_eq_zero.mp hy')
  · intro h
    have : (1 : O) • x = 0 := LinearMap.congr_fun h (Submodule.Quotient.mk 1)
    exact hx0 (by simpa using this)

theorem cls_eq_zero [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    {M : Type} [AddCommGroup M] [Module O M] [Module.Flat O M] (W : Representation O G M) (χ : G →* Oˣ)
    (cls : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H1 (twCoef W χ X) ⊤))
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (m : M ⊗[O] X),
      IsLocallyConstant fun g => twCoef W χ X g m)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], 0 ∈ cls X)
    (hmap : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X]
      (X' : Type) [AddCommGroup X'] [Module O X'] [Finite X'] (f : X →ₗ[O] X') (c : H1 (twCoef W χ X) ⊤),
      (c ∈ cls X → coefH1 W χ f c ∈ cls X') ∧ (Function.Injective f → coefH1 W χ f c ∈ cls X' → c ∈ cls X))
    (hres : ∀ (s : ℕ) (c : Fin s → H1 (twCoef W χ (O ⧸ Ideal.span {lam})) ⊤),
      (∀ a, c a ∈ cls (O ⧸ Ideal.span {lam})) → IndepMod lam c → s ≤ 0)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : cls X = {0} := by
  have hk : ∀ c ∈ cls (O ⧸ Ideal.span {lam}), c = 0 := by
    intro c hc
    by_contra hne
    have := hres 1 (fun _ => c) (fun _ => hc) (by
      intro x hx a
      rw [Fin.sum_univ_one] at hx
      rw [Subsingleton.elim a 0, ← Ideal.mem_span_singleton, ← hl.maximalIdeal_eq]
      intro hu
      exact hne (hu.smul_eq_zero.mp hx))
    omega
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨h0 X, ?_⟩
  generalize hn : Nat.card X = n
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    intro c hc
    rcases subsingleton_or_nontrivial X with hX | hX
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      have : z = 0 := Subtype.ext (funext fun g => Subsingleton.elim _ _)
      rw [this, Submodule.Quotient.mk_zero]
    · obtain ⟨f, hfi, hf0⟩ := exists_res_inj hl X
      haveI : Finite (O ⧸ Ideal.span {lam}) := Finite.of_injective f hfi
      haveI : Finite (X ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
      have hlt : Nat.card (X ⧸ LinearMap.range f) < n := by
        rw [← hn, Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)]
        haveI : Nontrivial (LinearMap.range f) :=
          Submodule.nontrivial_iff_ne_bot.mpr (fun h => hf0 (LinearMap.range_eq_bot.mp h))
        have h1 : 1 < Nat.card (LinearMap.range f) := Finite.one_lt_card
        have h2 : 0 < Nat.card (X ⧸ LinearMap.range f) := Nat.card_pos
        nlinarith
      have hq := ih _ hlt (X ⧸ LinearMap.range f) rfl _
        ((hmap X _ (LinearMap.range f).mkQ c).1 hc)
      obtain ⟨c₀, hc₀⟩ := exists_mapH1_eq (π' := twCoef W χ (O ⧸ Ideal.span {lam})) (f.lTensor M)
        (fun g m => by
          induction m using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [coefRep_tmul]
          | add a b ha hb => simp only [map_add (f := _), ha, hb])
        ((LinearMap.range f).mkQ.lTensor M) _
        (Module.Flat.lTensor_preserves_injective_linearMap f hfi)
        (LinearMap.lTensor_surjective M (Submodule.mkQ_surjective _))
        (lTensor_exact M (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _))
        (hlc X) c hq
      have hc₀' : coefH1 W χ f c₀ = c := hc₀
      have := hk c₀ ((hmap _ X f c₀).2 hfi (hc₀' ▸ hc))
      rw [← hc₀', this, map_zero]

theorem isLocallyConstant_smul {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] {Y : Type} [AddCommGroup Y] [Module O Y]
    [Finite Y] (m : Y) : IsLocallyConstant fun a : ℤ_[l] => algebraMap ℤ_[l] O a • m := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  have hN : (Nat.card Y : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨Metric.ball a ‖(Nat.card Y : ℤ_[l])‖, Metric.isOpen_ball, Metric.mem_ball_self (norm_pos_iff.mpr hN), ?_⟩
  intro b hb
  rw [mem_ball_iff_norm] at hb
  have hd : (Nat.card Y : ℤ_[l]) ∣ b - a := by
    rcases ValuationRing.dvd_total (Nat.card Y : ℤ_[l]) (b - a) with h | ⟨d, hd⟩
    · exact h
    · exfalso
      rw [hd, norm_mul] at hb
      have := PadicInt.norm_le_one d
      nlinarith [norm_nonneg (b - a)]
  obtain ⟨d, hd⟩ := hd
  rw [← sub_eq_zero, ← sub_smul, ← map_sub, hd, mul_comm, map_mul, mul_smul, map_natCast,
    Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero', smul_zero]

end General

theorem isLocallyConstant_twCoef {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [Algebra ℤ_[l] O] (Γ : GalData G Qp LL O) (χ : G → ℤ_[l]ˣ) (hc : Continuous χ)
    (hε : ∀ g, (Γ.ε g : O) = algebraMap ℤ_[l] O (χ g)) (c : ℕ)
    (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] (m : O ⊗[O] Y) :
    IsLocallyConstant fun g => twCoef (Γ.Wchi c) Γ.χ₁ Y g m := by
  haveI : Finite (O ⊗[O] Y) := Finite.of_equiv _ (TensorProduct.lid O Y).toEquiv.symm
  have hε' : ∀ g, Γ.ε g = Units.map (algebraMap ℤ_[l] O : ℤ_[l] →* O) (χ g) := fun g => Units.ext (hε g)
  have h1 : Continuous fun g : G => (((χ g) ^ (-((c : ℤ) - 1)) : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (hc.zpow _)
  have h2 := (isLocallyConstant_smul (l := l) (O := O) m).comp_continuous h1
  convert h2 using 2 with g
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, hε', ← map_zpow]
  rfl

theorem exists_eps {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) :
    ∃ χ : S.G → ℤ_[l]ˣ, Continuous χ ∧ ∀ g, (S.Γ.ε g : S.O) = algebraMap ℤ_[l] S.O (χ g) := by
  obtain ⟨χ, hχ, hc, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  refine ⟨fun g => χ g, hc.comp continuous_subtype_val, fun g => ?_⟩
  apply Subtype.ext
  have h1 := S.hyp.2.1.2.2.2 g
  have h2 : ((P.PD S.K).χ g : ℚ_[l]) = (P.χQ g : ℚ_[l]) := P.PD_χ S.K g
  rw [h2, ← hχ] at h1
  exact h1

theorem zero_mem {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] {s : Set N}
    (h : ∃ A : Submodule O N, s = A) : 0 ∈ s := by
  obtain ⟨A, rfl⟩ := h
  exact A.zero_mem

theorem cls_eq_zero_of_flat {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] [Module.Flat S.O M] (W : Representation S.O S.G M) (hL : S.Lem0 W) (hR : S.ResBound W 0)
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] (m : M ⊗[S.O] X),
      IsLocallyConstant fun g => twCoef W S.Γ.χ₁ X g m)
    (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] : S.cls W X = {0} := by
  obtain ⟨⟨hD, hV, -⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hl : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact @cls_eq_zero S.O S.G _ _ _ hD hV _ hl M _ _ _ W S.Γ.χ₁
    (fun X _ _ => S.cls W X) hlc (fun Y _ _ _ => zero_mem (hL Y).1)
    (fun Y _ _ _ Y' _ _ _ f x => (hL Y).2.2 Y' f x) hR X _ _ _

theorem main : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), ∀ c : ℕ, S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0 → ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], S.cls (S.Γ.Wchi c) X = {0} := by
  intro l _ P S c hL hR X _ _ _
  exact cls_eq_zero_of_flat S _ hL hR
    (fun Y _ _ _ m => (exists_eps S).elim fun χ h => isLocallyConstant_twCoef S.Γ χ h.1 h.2 c Y m) X

end GlobalTheory.TopSteps.CharAllCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpMult

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_ddR (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ a ≤ DdR PD ρ :=
  le_trans inf_le_left inf_le_left

theorem jump_iff_of_finite [FiniteDimensional LL ↥(DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FiniteDimensional LL ↥(FildR PD ρ τ a) ∧ 0 ≤ multV PD ρ τ a ∧
      (IsJumpV PD ρ τ a ↔ multV PD ρ τ a ≠ 0) := by
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_ddR PD ρ τ a)
  have hle := fildR_succ_le PD ρ τ a
  refine ⟨this, ?_, ?_, ?_⟩
  · have := Submodule.finrank_mono hle
    unfold multV
    omega
  · intro hj h0
    apply hj
    apply Submodule.eq_of_le_of_finrank_eq hle
    unfold multV at h0
    omega
  · intro h h'
    exact h (by rw [multV, h', sub_self])

end General

theorem jump_iff_mult_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) ρ τ a) ∧ 0 ≤ multV (P.PD K) ρ τ a ∧ (IsJumpV (P.PD K) ρ τ a ↔ multV (P.PD K) ρ τ a ≠ 0) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ a
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact jump_iff_of_finite (P.PD K) ρ τ a

end GlobalTheory.Per.JumpMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmer
section
noncomputable section

namespace GlobalTheory.Cut.SelClass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem length_le_cob_add {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    (C : Submodule R (Γ → M)) (hC : C ≤ ReciprocityTheory.Gal.Z1 rho) (S : Submodule R (ReciprocityTheory.Gal.H1 rho))
    (hS : ∀ f (hf : f ∈ C), (Submodule.Quotient.mk ⟨f, hC hf⟩ : ReciprocityTheory.Gal.H1 rho) ∈ S) :
    Module.length R ↥C ≤ Module.length R ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) + Module.length R ↥S := by

  let ψ : ↥C →ₗ[R] ReciprocityTheory.Gal.H1 rho :=
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype).mkQ ∘ₗ Submodule.inclusion hC
  have hker : ∀ x : ↥C, ψ x = 0 → (x : Γ → M) ∈ ReciprocityTheory.Gal.B1 rho := by
    intro x hx
    have h := (Submodule.Quotient.mk_eq_zero _).1 hx
    simpa using h
  have hrange : LinearMap.range ψ ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hS x.1 x.2
  let K := LinearMap.ker ψ.rangeRestrict
  have hsplit := Module.length_eq_add_of_exact K.subtype ψ.rangeRestrict
    (Submodule.subtype_injective _) ψ.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map _)

  let j : ↥K →ₗ[R] ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) :=
    LinearMap.codRestrict (C ⊓ ReciprocityTheory.Gal.B1 rho) (C.subtype ∘ₗ K.subtype) (fun x => by
      refine ⟨x.1.2, hker x.1 ?_⟩
      have hx : ψ.rangeRestrict x.1 = 0 := x.2
      exact congrArg Subtype.val hx)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hK := Module.length_le_of_injective j hj
  have hI := Module.length_le_of_injective (Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)
  rw [hsplit]
  exact add_le_add hK hI


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem mk_mem_selG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (P : LocPrime l)
    (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
    (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (f : ↥(ReciprocityTheory.Gal.Z1 (WKG M)))
    (hl : ∀ w hw, (fun g => Br.phi (nb w hw) k (f.1 (Br.ι (nb w hw) g).1)) ∈
      HfD (P.PD (nb w hw).Kw) (Br.lat (nb w hw) (M.comp (Dec (F := E) (A.1 w)).subtype)))
    (hu : ∀ v, v ∉ placesOver E l → v ∉ Sig → ∀ g ∈ Ine (F := E) (A.1 v), f.1 g = 0) :
    (Submodule.Quotient.mk f : ReciprocityTheory.Gal.H1 (WKG M)) ∈ Br.selG A l P nb Sig M := by
  unfold Br.selG GaloisCohomology.SelAll GaloisCohomology.bkCond Br.LlG Sel
  refine (Submodule.mem_iInf _).2 fun v => ?_
  rw [Submodule.mem_comap]
  dsimp only
  split_ifs with h1 h2 h3
  · unfold Br.bkG
    refine Submodule.mem_map.2 ⟨_, ?_, rfl⟩
    exact hl v h2
  · exact Submodule.mem_top
  · exact Submodule.mem_top
  · have hv : v ∉ placesOver E l := h1
    unfold GaloisCohomology.unrAt H1ur
    rw [LinearMap.mem_ker]
    unfold ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

    convert (ReciprocityTheory.Gal.B1 _).zero_mem using 1
    funext g
    exact hu v hv h3 _ g.2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  intro D i ρ π C hC hfin hine
  unfold lenCob
  refine length_le_cob_add _ C hC _ (fun f hf => ?_)
  unfold Br.selPi
  refine mk_mem_selG D.nd.plOm (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i) _ (WpO D.nd i ρ π) ⟨f, hC hf⟩ ?_ ?_
  · intro w hw
    exact hfin f hf w hw
  · intro v hv hSig g hg
    have hSv : v ∉ D.nd.S i := fun h => hSig (Or.inl h)
    have hQv : v ∉ D.nd.Q i := fun h => hSig (Or.inr h)

    have hmem : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) D.R.r) Subtype.val f ∈ resIne i C v :=
      Submodule.mem_map_of_mem hf
    rw [hine v hv hSv hQv, Submodule.mem_bot] at hmem
    exact congrFun hmem ⟨g, hg⟩

end GlobalTheory.Cut.SelClass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapEqProdOfValuationSubring
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem map_eq_prod_of_valuationSubring {O A K F : Type} [CommRing O] [Field K] [CommRing F]
    (B : ValuationSubring K) (j : O →+* K) (φ : B →+* F) (ψ : O →+* F)
    (h : ∀ y, ∃ h : j y ∈ B, φ ⟨_, h⟩ = ψ y) (t : A → K) (ι : A → F)
    (ht : ∀ x, ∃ h : t x ∈ B, ι x = φ ⟨_, h⟩) (p : O[X]) (s : Multiset A)
    (hp : p.map j = (s.map fun x => X - C (t x)).prod) :
    p.map ψ = (s.map fun x => X - C (ι x)).prod := by

  let j' : O →+* B :=
    { toFun := fun y => ⟨j y, (h y).1⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun a b => Subtype.ext (map_mul j a b)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j a b) }
  let t' : A → B := fun x => ⟨t x, (ht x).1⟩
  have hψ : ψ = φ.comp j' := by
    ext y
    exact ((h y).2).symm
  have hj : B.subtype.comp j' = j := by
    ext y
    rfl
  have hB : p.map j' = (s.map fun x => X - C (t' x)).prod := by
    apply Polynomial.map_injective B.subtype Subtype.val_injective
    rw [Polynomial.map_map, hj, hp, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hψ, ← Polynomial.map_map, hB, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [(ht x).2]

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ) (b : P.R.BdR), (∀ n : ℕ, b ∈ Lat AI M n) → b ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | exact GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.mem_FilB_of_forall_Lat <;> assumption)
end

