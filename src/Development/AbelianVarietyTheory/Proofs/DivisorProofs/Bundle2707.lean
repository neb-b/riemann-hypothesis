module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensAct

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) [Module O D'.X]
    (o : D'.OAct O) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (i : Fin r) :
    TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) i = ∏ j, TensTor.cmp T ν ν' b j ^ ρ x i j := by
  letI := D.P.isAb.comm
  simp only [TensTor.cmp, GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x i]
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := by simp [Hom.one_def]
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have := map_prod (ν.eA.symm.toMonoidHom.comp P) (fun j => T.pr j ^ ρ x i j) Finset.univ
  simp only [map_zpow] at this
  exact this

end GlobalTheory.Mum.TensAct
namespace GlobalTheory.Mum.TensAct

section V
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem rel_one (hF : TensFacts W φ e wv) : GtRelV W φ e wv 1 1 := by
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.Mum.TensTor.VExist.gtRelV_exists F N N' W φ e wv hF 1
  have h2 := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv hF u u 1 1 hu hu
  rw [_root_.mul_one] at h2
  have h3 : u * u = u := _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W φ e wv hF _ _ _ h2 hu
  rw [_root_.mul_eq_left] at h3
  exact h3 ▸ hu

theorem rel_pow (hF : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) :
    ∀ m : ℕ, GtRelV W φ e wv (v' ^ m) (vs ^ m)
  | 0 => by simpa using rel_one hF
  | m + 1 => by
    rw [_root_.pow_succ, _root_.pow_succ]
    exact _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv hF _ _ _ _ (rel_pow hF h m) h

end V

theorem io_sum {O : Type} [CommRing O] (N : NumD O) {κ : Type} (s : Finset κ) (m : κ → ℤ) (y : κ → N.X) :
    N.io (∑ j ∈ s, m j • y j) = ∏ j ∈ s, N.io (y j) ^ m j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, N.io_add, ih]
    congr 1
    have := N.ioHom.map_zpow (Multiplicative.ofAdd (y k)) (m k)
    simpa [NumD.ioHom, ← ofAdd_zsmul] using this

def qTH {O : Type} [CommRing O] (N : NumD O) (k : ℕ) : Multiplicative N.X →* N.QT k :=
  MonoidHom.mk' (fun z => N.qTriv k z.toAdd) fun a b => Subtype.ext (Prod.ext
    (by simp [NumD.qTriv, smul_add, ofAdd_add]) (by simp [NumD.qTriv, N.io_add]))

theorem qEq_iff_mk {O : Type} [CommRing O] (N : NumD O) {k : ℕ} (p p' : N.QT k) :
    N.QEq p p' ↔ (p : N.QT k ⧸ (qTH N k).range) = p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [qTH]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    have : N.qTriv k z.toAdd = p⁻¹ * p' := hz
    rw [this, mul_inv_cancel_left]

end GlobalTheory.Mum.TensAct

open GlobalTheory.Mum.TensAct in
theorem GlobalTheory.Mum.TensAct.qkAct_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact g ev hadd hker n hn x a p' q' hp hq
  letI := H.starRing
  have hF := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hR D D' W T F N N' ν ν'
  have hB := GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have hB' := GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  beta_reduce at hB hB'
  obtain ⟨q0, qs, hq0, hqs, hrel0⟩ := hp
  obtain ⟨q1, qs1, hq1, hqs1, hrel1⟩ := hq
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).1 o.onB x
  let us : Fin r → N.QT n := fun i => ∏ j, qs j ^ ρ x i j
  let ts : Fin r → N.Gt := fun i => ∏ j, (qs j).1.2 ^ ρ x i j
  have hts : ∀ i, (us i).1.2 = ts i := fun i => by
    show ((MonoidHom.snd _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j) = ∏ j, (qs j).1.2 ^ ρ x i j
    rw [map_prod]
    simp only [map_zpow]
    rfl
  have husy : ∀ i, (us i).1.1.toAdd = ∑ j, ρ x i j • (qs j).1.1.toAdd := fun i => by
    show Multiplicative.toAdd (((MonoidHom.fst _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j)) = _
    rw [map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow]
    rfl
  obtain ⟨w', hw'⟩ := _root_.GlobalTheory.Mum.TensTor.VExist.gtRelV_exists F N N' W _ _ _ hF ts
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x q0.1.2.b := by
    apply hF.2.1.1
    funext i
    rw [cmp_actV T ν ν' ρ o hact x _ i, hw'.1 i]
    simp only [ts]
    rw [← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, NumD.projB_apply, hrel0.2.1 j]
  have hros := GlobalTheory.T.rosati_values_tensor_data_matrix_action R hR D D' W T F N N' ν ν' E H ρ hρ o hact x ρ' hρ' q0.1.2 w' (fun j => (qs j).1.2) hrel0.2 hw'

  set y'' : N'.X := ν'.eX.symm (x • p'.y) with hy''
  have hey : ∀ i, TensTor.chi T ν ν' y'' i = (us i).1.1.toAdd := fun i => by
    rw [husy i]
    have h1 : ν'.eX y'' = x • p'.y := by rw [hy'', AddEquiv.apply_symm_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TensTor.chi, h1, hact.1 x p'.y i, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hrel0.1 j, ← hq0.1]
    rfl
  have hwn : w' ^ n = N'.io y'' := by
    have hpow := rel_pow hF hw' n
    have hio := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W _ _ _ hF y''
    have e1 : ts ^ n = fun j => N.io (TensTor.chi T ν ν' y'' j) := funext fun i => by
      rw [hey i, husy i, io_sum]
      simp only [Pi.pow_apply, ts, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← (qs j).2]
      rw [← zpow_natCast, ← zpow_natCast ((qs j).1.2), ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e1] at hpow
    exact _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W _ _ _ hF _ _ _ hpow hio
  let tv : N'.QT n := ⟨(Multiplicative.ofAdd y'', w'), by rw [NumD.mem_QT]; exact hwn⟩
  obtain ⟨t', ht'⟩ := (hB'.2.2.2.2 n).2.1 tv

  have hex : ∀ b, ∃ c, ν.QPt (ev n b) c := fun b => ((hB.2.2.2.2 n).1 (ev n b)).exists
  choose qv hqv using hex
  have huniq : ∀ b c, ν.QPt (ev n b) c → c = qv b := fun b c h =>
    ((hB.2.2.2.2 n).1 (ev n b)).unique h (hqv b)
  have haddv : ∀ b c, N.QEq (qv b * qv c) (qv (b + c)) := fun b c => by
    obtain ⟨q, hqy, hqadd, hqeq⟩ := hadd n hn b c
    obtain ⟨cq, hcq⟩ := ((hB.2.2.2.2 n).1 q).exists
    have e1 : cq = qv b * qv c := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        change ν.eX cq.1.1.toAdd = ν.eX ((qv b).1.1.toAdd + (qv c).1.1.toAdd)
        rw [map_add (f := _), (hqv b).1, (hqv c).1, hcq.1, hqy]
      · exact (hB.2.2.1 _ _ _ _ _ _ (hqv b).2 (hqv c).2 hcq.2).1 hqadd
    rw [← e1]
    exact ((hB.2.2.2.2 n).2.2 q (ev n (b + c)) cq (qv (b + c)) hcq (hqv _)).1 hqeq
  let f : Multiplicative ((Fin g → ℤ) × (Fin g → ℤ)) →* N.QT n ⧸ (qTH N n).range :=
    MonoidHom.mk' (fun b => ((qv b.toAdd : N.QT n) : N.QT n ⧸ (qTH N n).range)) fun b c => by
      rw [toAdd_mul, ← (qEq_iff_mk N _ _).1 (haddv _ _), QuotientGroup.mk_mul]
  have hQi : ∀ i, N.QEq (us i) (qs1 i) := fun i => by
    rw [qEq_iff_mk, huniq _ _ (hqs1 i)]
    have h1 : ((qv (∑ j, ρ x i j • a j) : N.QT n) : N.QT n ⧸ (qTH N n).range) =
        f (Multiplicative.ofAdd (∑ j, ρ x i j • a j)) := rfl
    rw [h1, ofAdd_sum, map_prod]
    simp only [us, QuotientGroup.mk_prod, QuotientGroup.mk_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ofAdd_zsmul, map_zpow, huniq _ _ (hqs j)]
    rfl
  choose z hz1 hz2 using hQi
  obtain ⟨z', hz'⟩ := hF.2.2.2.1.2 z
  let eH : N'.X →+ (Fin r → N.X) := AddMonoidHom.mk' (TensTor.chi T ν ν') fun a b => funext (hF.2.2.1 a b)
  have hQ : N'.QEq tv q1 := by
    refine ⟨z', ?_, ?_⟩
    · apply hF.2.2.2.1.1
      have hs : TensTor.chi T ν ν' (y'' + n • z') = TensTor.chi T ν ν' y'' + n • TensTor.chi T ν ν' z' :=
        (map_add eH _ _).trans (congrArg _ (map_nsmul eH n z'))
      change TensTor.chi T ν ν' q1.1.1.toAdd = TensTor.chi T ν ν' (y'' + n • z')
      rw [hs]
      funext i
      rw [Pi.add_apply, Pi.smul_apply]
      rw [hrel1.1 i, hz1 i, hey i, hz']
    · have hm := _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W _ _ _ hF _ _ _ _ hw' (_root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W _ _ _ hF z')
      have e2 : ts * (fun j => N.io (TensTor.chi T ν ν' z' j)) = fun j => (qs1 j).1.2 := funext fun i => by
        rw [Pi.mul_apply, hz2 i, hts i, hz']
      rw [e2] at hm
      exact _root_.GlobalTheory.Mum.TensTor.gtRelV_unique F N N' W _ _ _ hF _ _ _ hrel1.2 hm
  refine ⟨t', ?_, ?_, ((hB'.2.2.2.2 n).2.2 t' q' tv q1 ht' hq1).2 hQ⟩
  · rw [← ht'.1]
    exact AddEquiv.apply_symm_apply _ _
  · exact ((GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).2 o x ρ' hρ' p'.g t'.g q0.1.2 w'
      hq0.2 ht'.2).2 ⟨hb, hros⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaLevels

variable {R : Type} [CommRing R] [IsDomain R]

def galPt {A : PolAV (Sp (FractionRing R))} (σ : Kb R →ₐ[FractionRing R] Kb R) (y : TFK (R := R) (Kb R) ⟶ A.A) :
    TFK (R := R) (Kb R) ⟶ A.A :=
  Over.homMk (spMap σ.toRingHom ≫ y.left) (by
    rw [Category.assoc, Over.w y]
    show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) σ.comp_algebraMap)

theorem conj_eq_of_pow_eq_one [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hT : OneTrait D.toPre A lab) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : Kb R) ≠ 0) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (hQ : ∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p')
    (hA : ∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ n = 1 → spMap σ.toRingHom ≫ y.left = y.left)
    {M d : ℕ} (hd : 1 ≤ d) (hM : M = n * d) (x₂ : QkPt D.toPre (Kb R) M → (TFK (R := R) (Kb R) ⟶ A.A))
    (hx₂ : ∀ p p', QkExt σ.toRingHom p p' → (x₂ p').left = spMap σ.toRingHom ≫ (lab M p).left)
    (h₂ : LabTors D.toPre A M x₂) (p' : QkPt D.toPre (Kb R) M) (hp' : lab M p' ^ n = 1) : x₂ p' = lab M p' := by
  subst hM
  have hnd : 1 ≤ n * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have T₁ := _root_.GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait R hR D A lab hT n hn
  have T₂ := _root_.GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait R hR D A lab hT (n * d) hnd
  obtain ⟨r, hr⟩ := T₁.1 _ hp'
  obtain ⟨q, hqy, hqg⟩ := _root_.GlobalTheory.Mum.QkMul.exists_qk_mul R D (Kb R) n d r
  have hq : lab (n * d) q = lab n r := _root_.GlobalTheory.Mum.lab_level_mul R hR D A lab hT n d hn hd r q hqy hqg
  have hqp : QkPt.Equiv D.toPre (Kb R) q p' := (T₂.2.2.1 q p').1 (hq.trans hr)
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hnK r
  obtain ⟨q₀, hq₀y, hq₀g⟩ := _root_.GlobalTheory.Mum.QkMul.exists_qk_mul R D (Kb R) n d r₀
  have hq₀ : QkExt σ.toRingHom q₀ q := by
    obtain ⟨y, g, e⟩ := q
    obtain ⟨y₀, g₀, e₀⟩ := q₀
    dsimp only at hqy hqg hq₀y hq₀g
    subst hqg hq₀g hqy hq₀y
    exact ⟨congrArg (d • ·) hr₀.1, hr₀.2.1, hr₀.2.2⟩
  have e₂ := hx₂ q₀ q hq₀
  rw [_root_.GlobalTheory.Mum.lab_level_mul R hR D A lab hT n d hn hd r₀ q₀ hq₀y hq₀g, (T₁.2.2.1 r₀ r).2 (hQ r₀ r hr₀), hr, hA _ hp'] at e₂
  exact ((h₂.2.2.1 q p').2 hqp).symm.trans (Over.OverMorphism.ext e₂)

end GlobalTheory.Mum.ThetaLevels


open GlobalTheory.Mum.ThetaLevels in
theorem GlobalTheory.Mum.thetaLevels_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  intro R _ _ _ hR n hn ho hu D A lab hT hG
  have hch : CharZero R := hR.2
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ j₀ * (n ^ 2) ^ 2 := by
    refine ⟨((n ^ 2) ^ 2) ^ A.g * A.g.factorial, ?_⟩
    have h1 : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ (((n ^ 2) ^ 2) ^ A.g * A.g.factorial) :=
      Nat.lt_pow_self hn.one_lt
    have h2 : 1 ≤ (n ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ h2)
  refine ⟨j₀ + 4, fun i hi v hv hc σ p p' hpp' => ?_⟩
  have hmj : n ^ i = n ^ (i - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hbound : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < (n ^ i) := by
    rw [hmj]
    exact lt_of_lt_of_le hj₀ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn.pos (by omega)))
  have hF : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hKc : CharZero (Kb R) := charZero_of_injective_algebraMap (algebraMap (FractionRing R) (Kb R)).injective
  have hMK : (((n ^ i) ^ 2 : ℕ) : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))
  choose pre hpre using fun p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hMK p'
  let x₂ : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A) := fun q => galPt σ (lab ((n ^ i) ^ 2) (pre q))
  have hx₂ : ∀ q q', QkExt σ.toRingHom q q' → (x₂ q').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) q).left := fun q q' h => by
    show spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) (pre q')).left = _
    rw [GlobalTheory.QkClosure.qkExt_inj σ.toRingHom σ.comp_algebraMap (hpre q') h]
  have hM1 : 1 ≤ (n ^ i) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ hn.ne_zero))
  have H₁ := _root_.GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait R hR D A lab hT ((n ^ i) ^ 2) hM1
  have H₂ := GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure R hR D A σ ((n ^ i) ^ 2) hM1 (lab ((n ^ i) ^ 2)) x₂ H₁ hx₂
  have Hn : ∀ q, lab ((n ^ i) ^ 2) q ^ n = 1 → x₂ q = lab ((n ^ i) ^ 2) q := fun q hq =>
    conj_eq_of_pow_eq_one hR D A lab hT hn.one_lt.le (Nat.cast_ne_zero.2 hn.ne_zero) σ (hG σ).1 (hG σ).2
      (d := n ^ (2 * i - 1)) (Nat.one_le_pow _ _ hn.pos)
      (by rw [← pow_mul, ← pow_succ']; congr 1; omega) x₂ hx₂ H₂ q hq
  obtain ⟨c, hc'⟩ := hc σ
  have h₁ := GlobalTheory.ThetaDescentLevel.isThetaPt_reindex hv pre
  have h₂ := GlobalTheory.T.thetaPoint_conj_algClosure_automorphism R A (n ^ i) σ _ (fun q => lab ((n ^ i) ^ 2) (pre q)) x₂ (fun q => v (pre q)) (fun q => rfl) h₁
  have h₃ : IsThetaPt A (n ^ i) x₂ (fun q => GlobalTheory.Ex.fnOf (v q)) :=
    GlobalTheory.Ex.ThetaDescent.isThetaPt_unit_mul A (n ^ i) x₂ _ _ (GlobalTheory.Ex.fnOf ((c⁻¹ : (Kb R)ˣ) : Kb R))
      ((Units.isUnit c⁻¹).map _) (fun q => by
        unfold GlobalTheory.Ex.fnOf
        rw [← map_mul, hc' _ _ (hpre q), ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]) h₂
  have key := GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n R D.toPre A n (i - 4) (n ^ i) hn ho hmj hbound (lab ((n ^ i) ^ 2)) x₂ H₁ H₂ Hn v hv h₃ p'
  rw [← key]
  exact hx₂ p p' hpp'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.Poinc

theorem rechart_at_classical_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  have h1 : X₁.π ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∈ Set.range i := by
    have e1 := congrArg (fun f : Sp (PadicAlgCl p) ⟶ Z => f (closedPoint (PadicAlgCl p))) c.comm
    simp only [Scheme.Hom.comp_apply] at e1
    exact ⟨_, by simp only [Scheme.Hom.comp_apply]; exact e1.symm⟩
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hU, hwU, -, hSame, hi₀, hdiag', hpt⟩ :=
    _root_.GlobalTheory.Poinc.exists_rechart_affine g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag _ h1
  set w := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X₁.M.ringOn U ≤ X₁.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ c.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X₁.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ c.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X₁.M.ringOn U, y₀ a = X₁.M.val (gPt p ≫ c.y) a := fun a => rfl

  let e : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z :=
    Spec.map (CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X₁.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X₁.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ c.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ c.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X₁.M.ringOn U).val.toRingHom ≫ e = X₁.M.pt := by
    refine ext_of_valR hU (he _).1 (X₁.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (X₁.M.ringOn U).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsSeparated X₁.z := X₁.isProper_compactificationMap.toIsSeparated
  have hgen2 : spMap (X₁.M.ringOn U).val.toRingHom ≫ (e ≫ X₁.π) =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (u' ≫ i) := by
    rw [← Category.assoc, hgen, X₁.comp, ← Category.assoc _ u' i, hpt, Category.assoc]
  have hb : e ≫ X₁.π = u' ≫ i :=
    ext_of_isDominant_of_isSeparated X₁.z
      (ext_of_isDominant (spMap (X₁.M.ringOn U).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (X₁.M.ringOn U).val.toRingHom) hgen2
  haveI := himm
  have hpt' : spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y := by
    rw [← cancel_mono i, Category.assoc, ← hb, ← Category.assoc, ha, Category.assoc, c.comm, Category.assoc]

  let τ := Spec.preimage (c.y ≫ X₁.M.s)
  have hσ : (gPt p ≫ c.y) ≫ X₁.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (c.y ≫ X₁.M.s), ← Spec.map_comp]; rfl
  refine ⟨c₀, hc, X₁.M.ringOn U, fg, frac, hth', hev, ρ', ε', u', hSame, hi₀, hle, hdiag', y₀, hy₀, hpt',
    fun a => ?_⟩
  rw [hy₀]
  show ‖X₁.M.val (gPt p ≫ c.y) (algebraMap X₁.o₁ X₁.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hku hζ Wo h ξ₁' ξ₂' hh h₁ h₂ F₁ _ _ _ F₂ _ _ _ c x₁ x₂ hx₁ hx₁g hx₂ hx₂g
  have hw₁ : o₁ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hw₂ : o₂ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hA := GlobalTheory.T.toricTorsionSection_eq_torusPoint_at_closedPointField B H V₁ hV₁ G₁ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ (ξ₁' ≫ h) (by rw [Category.assoc, hh, h₁]) k (o₁ ζ) hk hw₁
    F₁ c x₁ hx₁ hx₁g
  obtain ⟨κ, _, b, hb, Gκ, _, m, hm, τ, z, hτ, hz, he⟩ := _root_.GlobalTheory.SpreadTorSection.trait_section B H hH V₁ G₁ D₁ A₁ U₁ ξ₁ β₁ V₂ G₂ D₂ A₂ U₂ ξ₂ β₂ ρ
    hS o s o₁ o₂ hs₁ hs₂ k ζ hk hζ Wo h ξ₁' ξ₂' hh h₁ h₂ c hA
  exact GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField B H V₂ hV₂ G₂ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ (ξ₂' ≫ h) (by rw [Category.assoc, hh, h₂]) k (o₂ ζ) hk
    (by simpa using hku.map o₂) hw₂ F₂ (c.comp ρ) x₂ hx₂ hx₂g κ b hb Gκ m hm τ hτ z hz he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNorm
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem torsor_point_of_essFiniteType : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  obtain ⟨A', _, _, _, _, _, _, EA', _, _, _, _, _, QA', _, hQ', hq', ρ', hρ1, hρ2, jA', ψA', hψ', DA', _, _,
    actA', htor', hgood', β, h, hβ1, hβ2⟩ :=
    GlobalTheory.T.strictHenselisation_enlarge_good_at_origin T O hT P φ hφ hsh hP q hq0 hqT A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htor
  have hce := GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType A' EA' QA' hQ' ρ' hρ1 hρ2 q hq0 hq' DA' actA' htor' hgood'
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsSepClosed (ResidueField O) := hsh.2.1
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian A' (Localization.AtPrime QA') O (GlobalTheory.LocAcyc.GenFib T O) jA'
    (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)) ψA' hψ' DA' htor'.1 hce
  refine ⟨σ'.comp h, ?_⟩
  rw [RingHom.comp_assoc, hβ2, ← RingHom.comp_assoc, hσ', hβ1]

end GlobalTheory.KeyOriginNoeth
end

