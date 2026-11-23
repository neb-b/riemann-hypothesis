module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
section
noncomputable section

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {l : ℕ} [Fact l.Prime]

def FaithH {P : LocPrime l} (AI : LocAinf l P) : Prop :=
  ∀ (L : FinExt l) (g : GQ l), P.χQ g = 1 →
    (∀ x : OCb l, (∀ h ∈ GK L, P.χQ h = 1 → AI.actT h x = x) → AI.actT g x = x) → g ∈ GK L

variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}

def FixH (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l} (x : RW LL) : Prop :=
  ∀ g ∈ GK K, P.χQ g = 1 → AI.gRW LL g x = x

def FixBasis (AI : LocAinf l P) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {r : ℕ}
    (e : Module.Basis (Fin r) (RW LL) (TW (RW LL) T)) : Prop :=
  ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (e i) = e i

def EtBasis {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {r : ℕ}
    (e : Module.Basis (Fin r) (RW LL) (TW (RW LL) T)) : Prop :=
  FixBasis AI T e ∧ ∀ i j, e.repr (TWmap (φRW LL) T (e j)) i ∈ Set.range I.ioE

def WachEx {P : LocPrime l} (AI : LocAinf l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ E : WEt I, Nonempty (NS E)

def Conv (a : PowerSeries ↥LL.1) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k a : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)

def IsExp (ζ : ↥LL.1) (a e : PowerSeries ↥LL.1) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => ((PowerSeries.coeff k
    (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) (PowerSeries.trunc m a)) : ↥LL.1) : Om l))
    Filter.atTop (nhds ((PowerSeries.coeff k e : ↥LL.1) : Om l))

def logS (LL : FinExt l) : PowerSeries ↥LL.1 :=
  PowerSeries.mk fun k => (-1 : ↥LL.1) ^ (k + 1) / (k : ↥LL.1)

def toLL {n : ℕ} (a : LetA ↥(OL LL) n) : LetA ↥LL.1 n :=
  fun i => PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (a i)

def IsBeta (AI : LocAinf l P) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) : Prop :=
  ∀ (o : ↥(OL LL)) (w : Ainf l), β (o ⊗ₜ[ℤ_[l]] w) = (o : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w

structure IsEval {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B)
    (J : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1 ⊗[ℚ_[l]] P.R.B) : Prop where
  add : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a + b) = J a + J b
  mul : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a * b) = J a * J b
  smul : ∀ (c : ↥LL.1) a, (∀ i, Conv (a i)) → J (c • a) = c • J a
  ext : ∀ a, J (toLL a) = β (I.io a)
  frob : ∀ a, (∀ i, Conv (a i)) →
    J (fun i => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (i - 1))) =
      Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (J a)
  gal : ∀ (g : ↥(GK K)) a, (∀ i, Conv (a i)) →
    J (fun i => PowerSeries.subst
        (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ (Γ.resΓ g) PowerSeries.X)) (a i)) =
      Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ (g : GQ l)).toAlgHom (J a)
  log : J (fun _ => logS LL) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ s)⁻¹) • P.tB)
  taylor : ∀ i (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR),
    (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) →
    ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ a, (∀ j, Conv (a j)) → ∀ e, IsExp ζ (a i) e → ∀ m : ℕ,
    Algebra.TensorProduct.productMap ι P.ιB (J a) -
      ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k e) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈
        (P.PD K).Fil (m : ℤ)

end GlobalTheory.HWL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
section
noncomputable section

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA} {E : WEt I} {Zl : Type} [CommRing Zl] {zl : PowerSeries Zl →+* LetA O n}

def Sand (Mo : WN E zl) (T : LocLat G Qp LL O) (w : RA) : Prop :=
  (∀ x ∈ Mo.N T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x) ∧
    ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ Mo.N T, z = inclR a • E.jD T y}

end GlobalTheory.HWL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnramifiedSubfieldLeCyclotomicExt
section
noncomputable section

namespace GlobalTheory.NL.Model

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.conv_finite (e : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j e • u (k - (j : ℤ))).Finite := by
  refine (Set.finite_Iic (k - m).toNat).subset fun j hj => ?_
  simp only [Function.mem_support] at hj
  simp only [Set.mem_Iic]
  by_contra hlt
  push_neg at hlt
  exact hj (by rw [hm _ (by omega), smul_zero])

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.conv_one (u : ℤ → M) :
    _root_.GlobalTheory.NL.conv (1 : PowerSeries L) u = u := by
  funext k
  rw [_root_.GlobalTheory.NL.conv, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.mem_latSpan {ι : Type} (ex : ι → ℤ → M) (x : ι) :
    ex x ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex :=
  Submodule.subset_span ⟨1, x, (_root_.GlobalTheory.NL.Model.conv_one _).symm⟩

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
private theorem conv_mem_and_vanish_below (e : PowerSeries L) (D : Submodule L M)
    {u : ℤ → M} (hu : ∀ k, u k ∈ D) {m : ℤ} (hm : ∀ k < m, u k = 0) :
    (∀ k, _root_.GlobalTheory.NL.conv e u k ∈ D) ∧
      ∀ k < m, _root_.GlobalTheory.NL.conv e u k = 0 := by
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [_root_.GlobalTheory.NL.conv,
      finsum_eq_sum _ (_root_.GlobalTheory.NL.Model.conv_finite e hm k)]
    exact Submodule.sum_mem _ fun j _ => D.smul_mem _ (hu _)
  · rw [_root_.GlobalTheory.NL.conv]
    refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [hm _ (by omega), smul_zero]


open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.NL.Model.latSpan_coeff {ι : Type} (ex : ι → ℤ → M)
    (D : Submodule L M) (hD : ∀ x k, ex x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (f : ℤ → M) (hf : f ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex) :
    (∀ k, f k ∈ D) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, x, rfl⟩ := hg
    obtain ⟨m, hm⟩ := hs x
    obtain ⟨h1, h2⟩ := conv_mem_and_vanish_below e D (hD x) hm
    exact ⟨h1, m, h2⟩
  | zero => exact ⟨fun _ => D.zero_mem, 0, fun _ _ => rfl⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨h1, m, hm⟩ := hg
    obtain ⟨h1', m', hm'⟩ := hg'
    refine ⟨fun k => D.add_mem (h1 k) (h1' k), min m m', fun k hk => ?_⟩
    simp [hm k (lt_of_lt_of_le hk (min_le_left _ _)), hm' k (lt_of_lt_of_le hk (min_le_right _ _))]
  | smul c g _ hg =>
    obtain ⟨h1, m, hm⟩ := hg
    exact ⟨fun k => D.smul_mem c (h1 k), m, fun k hk => by simp [hm k hk]⟩

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
theorem _root_.GlobalTheory.NL.Model.mem_van (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (i : ZMod n) (ζ : LL)
    (k : ℕ) (a : _root_.Formalism.BasicNotions.LetA O n) :
    a ∈ _root_.GlobalTheory.NL.van W i ζ k ↔
      ∀ j < k, PowerSeries.coeff j (W.lev i ζ a) = 0 := by
  rw [_root_.GlobalTheory.NL.van, Ideal.mem_comap, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]


open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
theorem _root_.GlobalTheory.NL.Model.pi_van_one (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (i : ZMod n) :
    (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∈ _root_.GlobalTheory.NL.van W i 1 1 ∧
      (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) ∉ _root_.GlobalTheory.NL.van W i 1 2 := by
  obtain ⟨E, h0, hd, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have hlev : W.lev i 1 _root_.Formalism.BasicNotions.letπ = E - 1 := by
    rw [map_one, one_mul] at hE
    rw [← hE]
    ring
  have h1 : PowerSeries.coeff 1 E = 1 := by
    have := congrArg (PowerSeries.coeff 0) hd
    simp only [PowerSeries.coeff_derivative] at this
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0] at this
    simpa using this
  simp only [_root_.GlobalTheory.NL.Model.mem_van, hlev]
  refine ⟨fun j hj => ?_, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    simp [h0]
  · have := h 1 (by norm_num)
    simp [h1] at this

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
theorem _root_.GlobalTheory.NL.Model.FilAt_anti (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    _root_.GlobalTheory.NL.FilAt (PD := PD) T τ (a + 1) ≤ _root_.GlobalTheory.NL.FilAt (PD := PD) T τ a := by
  refine sup_le_sup_right ?_ _
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FildR _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  refine inf_le_inf_left _ ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul w b => exact ⟨w ⊗ₜ ⟨b, PD.Fil_anti a b.2⟩, rfl⟩
  | add y z hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in
theorem _root_.GlobalTheory.NL.Model.ex_mem_Lat (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ x ∈ _root_.GlobalTheory.NL.Lat C h T i ζ :=
  _root_.GlobalTheory.NL.Model.mem_latSpan _ x


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in
theorem _root_.GlobalTheory.NL.Model.Lat_coeff (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F)
    (h : _root_.Formalism.BasicNotions.Loc.Good K s LL) (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K)
    (ζ : ↥LL.1) (f : ℤ → T.V ⊗[ℚ_[l]] P.R.B) (hf : f ∈ _root_.GlobalTheory.NL.Lat C h T i ζ) :
    (∀ k, f k ∈ _root_.GlobalTheory.NL.Di H h T i) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 :=
  _root_.GlobalTheory.NL.Model.latSpan_coeff _ _
    (fun x k => (C.C K s LL h).tie.levB_mem T i ζ x k)
    (fun x => (C.C K s LL h).tie.levB_supp T i ζ x) f hf

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem periodTensor_ιV_injective (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) :
    Function.Injective (_root_.Formalism.WeaklyAdmissibleFiltrations.ιV PD : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] BdR) := by
  have hf : Function.Injective ((PD.ι.toLinearMap).restrictScalars Qp) := PD.ι_inj
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) _ hf

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem levB_smul_eq_powerSeriesSmul_lemma_2 {Zl Ai : Type} [CommRing Zl] [CommRing Ai]
    [Algebra Zl O] [Algebra Zl Ai] {W : _root_.Formalism.BasicNotions.LocWach PD LL O v n} {RW : Type} [CommRing RW]
    [Algebra O RW] {inclR : TensorProduct Zl O Ai →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → RW →ₐ[O] RW} {πA : TensorProduct Zl O Ai}
    {E : _root_.Formalism.BasicNotions.EtTie W (TensorProduct Zl O Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai}
    {tS zS : BdR} (S : _root_.Formalism.BasicNotions.CmpTie W E ιdR p1 tS zS) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (a : _root_.Formalism.BasicNotions.LetA O n) (x : ↥(W.N T)) :
    S.levB T i ζ (a • x) = _root_.GlobalTheory.NL.conv (W.lev i ζ a) (S.levB T i ζ x) := by
  funext k
  refine periodTensor_ιV_injective (PD := PD) T ?_
  obtain ⟨m, hm⟩ := S.levB_supp T i ζ x
  rw [← S.levN_eq, W.levN_smul, _root_.GlobalTheory.NL.conv,
    map_finsum _ (_root_.GlobalTheory.NL.Model.conv_finite _ hm k)]
  simp only [map_smul, S.levN_eq]


open TensorProduct in
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l} in
theorem _root_.GlobalTheory.NL.Model.ex_smul (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1) (a : _root_.GlobalTheory.NL.AA K LL)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ (a • x) =
      _root_.GlobalTheory.NL.conv ((H.W K s LL h).lev i ζ a) (_root_.GlobalTheory.NL.ex C h T i ζ x) :=
  by
    set_option synthInstance.maxHeartbeats 400000 in
      exact levB_smul_eq_powerSeriesSmul_lemma_2 (C.C K s LL h).tie T i ζ a x


end Concrete

end GlobalTheory.NL.Model
end
end

