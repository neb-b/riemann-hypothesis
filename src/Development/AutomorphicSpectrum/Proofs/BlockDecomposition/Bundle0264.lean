module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcLoc

theorem dividedPowerFiltration_dividedPowersBot' (O : Type) [CommRing O] {r : ℕ} (hr : r ≠ 0) : pdP (dividedPowersBot O) r = ⊥ := by
  classical
  rw [eq_bot_iff]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have hq : ∃ q ∈ l, q.1 ≠ 0 := by
    by_contra h
    push_neg at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h q hq)
    omega
  obtain ⟨q, hq, h0⟩ := hq
  refine List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)
  rw [dividedPowersBot_dpow_eq]
  simp [h0]

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem sub_of_bot (a b : IdF F) (T : C) (h : a.S T = ⊥) : Subsingleton (sqM a b T) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := x.2
  have hy := y.2
  simp only [sqM, h, Ideal.map_bot] at hx hy
  exact (show (x.1 : F.obj T ⧸ b.S T) = 0 from hx).trans (show (y.1 : F.obj T ⧸ b.S T) = 0 from hy).symm

theorem sub_of_top (a b : IdF F) (T : C) (h : b.S T = ⊤) : Subsingleton (sqM a b T) := by
  haveI : Subsingleton (F.obj T ⧸ b.S T) := Ideal.Quotient.subsingleton_iff.2 h
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

theorem pi_ex (a b : IdF F) (T : C) {Y : Type} [CommRing Y] {P Q : Ideal Y} (e : Y ≃+* F.obj T)
    (hP : ∀ z, e z ∈ a.S T ↔ z ∈ P) (hQ : ∀ z, e z ∈ b.S T ↔ z ∈ Q) :
    ∃ π : P →+ sqM a b T, Function.Surjective π ∧ (∀ x, π x = 0 ↔ x.1 ∈ Q) ∧
      ∀ x, (π x).1 = Ideal.Quotient.mk _ (e x.1) := by
  refine ⟨AddMonoidHom.mk' (fun x => ⟨Ideal.Quotient.mk _ (e x.1), Ideal.mem_map_of_mem _ ((hP _).2 x.2)⟩)
    (fun x y => Subtype.ext (by simp)), ?_, fun x => ?_, fun x => rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    refine ⟨⟨e.symm w, (hP _).1 (by simpa using hw)⟩, Subtype.ext ?_⟩
    simp
  · rw [← hQ, ← Ideal.Quotient.eq_zero_iff_mem]
    exact Subtype.ext_iff

theorem theta_ex {G : Type} [CommRing G] [Algebra R G] (a b : IdF F) (T : C) (ht : a.S T = ⊤) (hb : b.S T = ⊥)
    (e : R ⊗[R] G ≃+* F.obj T) (he : ∀ r, e (r ⊗ₜ 1) = algebraMap R (F.obj T) r) :
    ∃ θ : G ≃ₗ[R] sqM a b T, ∀ x, (θ x).1 = Ideal.Quotient.mk _ (e (1 ⊗ₜ x)) := by
  let f : G →ₗ[R] sqM a b T :=
    { toFun := fun x => ⟨Ideal.Quotient.mk _ (e (1 ⊗ₜ x)), Ideal.mem_map_of_mem _ (by rw [ht]; trivial)⟩
      map_add' := fun x y => Subtype.ext (by simp [TensorProduct.tmul_add])
      map_smul' := fun r x => Subtype.ext (by
        have h1 : (1 : R) ⊗ₜ[R] (r • x) = (r ⊗ₜ[R] (1 : G)) * ((1 : R) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] (r • x))) = r • Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] x))
        rw [h1, map_mul, he, map_mul, Algebra.smul_def]
        rfl) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun x y h => ?_, ?_⟩, fun x => rfl⟩
  · have h1 := congrArg Subtype.val h
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb, Ideal.mem_bot, ← map_sub, map_eq_zero_iff _ e.injective, ← TensorProduct.tmul_sub] at h2
    have h3 := congrArg (TensorProduct.lid R G) h2
    simpa [sub_eq_zero] using h3
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨TensorProduct.lid R G (e.symm w), Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w))) = _
    have : (1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w) = e.symm w := by
      rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, e.apply_symm_apply]

end Sq

theorem crit_of {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (P : Poly Φ)
    {F a : ℤ → IdF Φ.A} {r r₀ : ℤ} (h : P.Crit F r₀) (h0 : a r = F r₀)
    (hk : ∀ k : ℕ, a (r - k) = F (r₀ - k)) : P.Crit a r := by
  intro T b
  rw [h0]
  simp only [hk]
  exact h T b

theorem chart_tens : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) (l s m : ℕ)
    (S : GrSplit O γ m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B)
      (hD : TO q l s {V} cO.D) (hD' : TS γ q l s {V} cA.D)
      (e : (⟨cO.D, hD⟩ : (TO q l s {V}).FullSubcategory) ⟶ (smO γ q l s {V}).G.obj ⟨cA.D, hD'⟩),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, e.hom.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f)) →
      ∀ (c t : ℤ), 0 ≤ c →
      ∀ (ha : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - c - i)) (sFil _ (t - c)))
        (hb : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - i)) (sFil _ t)),
      Tens O (N := S.N) (M := fun i => (sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).obj ⟨cO.D, hD⟩)
        (M' := (sq (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t)).obj ⟨cA.D, hD'⟩)
        fun i n x => ((smO γ q l s {V}).sqC (S.ν i n) (ha i n) (hb i n)).τ ⟨cA.D, hD'⟩
          (((sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).map e).hom x) := by
  intro O A _ _ _ I γ l s m S X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hD hD' e hiO hiA he c t hc ha hb
  haveI hF : Module.Flat O Γ(X, V) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale cV.t cV.etale
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have pO := (_root_.GlobalTheory.CompanionTheory.ChartFil.chart_grConst cO (GlobalTheory.T.chart_is_good cO) (TO q l s {V}) hQ hD).1
  have pA := (_root_.GlobalTheory.CompanionTheory.ChartFil.chart_grConst cA (GlobalTheory.T.chart_is_good cA) (TS γ q l s {V}) hQ' hD').1
  have bot1 : ∀ r : ℕ, r ≠ 0 → cO.D.pdPow r = ⊥ := fun r hr => by
    rw [pO, dividedPowerFiltration_dividedPowersBot' O hr, Ideal.map_bot]
  have mA : ∀ (r : ℕ) (z : A ⊗[O] Γ(X, V)), eA z ∈ cA.D.pdPow r ↔
      z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) := fun r z => by
    have h1 : cA.D.i = (eA : A ⊗[O] Γ(X, V) →+* cA.D.B).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) :=
      RingHom.ext fun a => (hiA a).symm
    rw [pA, h1, ← Ideal.map_map]
    constructor
    · intro h
      obtain ⟨w, hw, h2⟩ := (Ideal.mem_map_iff_of_surjective _ eA.surjective).1 h
      have h3 := eA.injective h2
      rwa [← h3]
    · exact fun h => Ideal.mem_map_of_mem _ h
  have fa : ∀ (i : Fin m) (hu : (t - c).toNat ≤ (i : ℕ)) (hv : (i : ℕ) < t.toNat),
      ∃ θ : Γ(X, V) ≃ₗ[O] sqM (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩,
        ∀ x, (θ x).1 = Ideal.Quotient.mk _ (eO (1 ⊗ₜ x)) := fun i hu hv =>
    theta_ex (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩
      (by
        change cO.D.pdPow _ = ⊤
        rw [show (t - c - i).toNat = 0 by omega]
        exact cO.D.pdPow_zero)
      (by
        change cO.D.pdPow _ = ⊥
        exact bot1 _ (by omega)) eO hiO
  choose θ hθ using fa
  obtain ⟨π, hs, hk, hπ⟩ := pi_ex (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t) ⟨cA.D, hD'⟩ eA (mA _) (mA _)
  refine GlobalTheory.T.graded_split_range_iso_of_interval (O := O) (A := A) (G := Γ(X, V)) γ m S (t - c).toNat t.toNat θ ?_ π hs hk _ ?_ ?_
  · intro i hi
    by_cases hu : (t - c).toNat ≤ (i : ℕ)
    · refine sub_of_top _ _ _ ?_
      change cO.D.pdPow _ = ⊤
      rw [show (t - i).toNat = 0 by
        have : ¬ (i : ℕ) < t.toNat := fun h => hi ⟨hu, h⟩
        omega]
      exact cO.D.pdPow_zero
    · refine sub_of_bot _ _ _ ?_
      change cO.D.pdPow _ = ⊥
      exact bot1 _ (by omega)
  · intro i n
    simp only [map_zero]
  · intro i n x hu hv hx
    refine Subtype.ext ?_
    rw [hπ]
    have hz := hθ i hu hv x
    generalize θ i hu hv x = z at hz ⊢
    obtain ⟨z, hz'⟩ := z
    change z = _ at hz
    subst hz
    have key : ∀ w : cA.D.B, w = eA (1 ⊗ₜ x) → cA.D.i (S.ν i n) * w = eA (S.ν i n ⊗ₜ x) := by
      rintro _ rfl
      rw [← hiA, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (Ideal.Quotient.mk _) (key _ (he x))

theorem bc_single : KH.LocBc → KH.PolyTf → BcOn True := by
  intro hLoc hPoly O A _ _ _ I γ l s m hO hA S X q 𝒱 h r r' hrr hrs ha hb j
  obtain ⟨-, V, d, rfl, ⟨cV⟩⟩ | ⟨hF, -⟩ := h
  swap
  · exact absurd trivial hF
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℤ, 0 ≤ c ∧ r = r' - c := ⟨r' - r, by omega, by ring⟩
  obtain ⟨cO, eO, tfO, hiO, htO, hevO⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (dividedPowersBot O) l s hO q
    (Ideal.Quotient.mk ⊥) (fun _ => rfl) cV
  obtain ⟨cA, eA, tfA, hiA, htA, hevA⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := A) γ l s hA q (κA O I) (fun _ => rfl) cV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chart_tensor_base_compat γ q cV cO cA eO eA hiO hiA hevO hevA
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hD : TO q l s {V} cO.D := ⟨tfO, V, rfl, cO.inV⟩
  have hD' : TS γ q l s {V} cA.D := ⟨tfA, V, rfl, cA.inV⟩
  have gO := GlobalTheory.T.chart_is_good cO
  have gA := GlobalTheory.T.chart_is_good cA
  let E := cO.frame gO (TO q l s {V}) hQ hD
  let E' := cA.frame gA (TS γ q l s {V}) hQ' hD'
  let e : E.D ⟶ (smO γ q l s {V}).G.obj E'.D := ObjectProperty.homMk e₀
  have he : (smO γ q l s {V}).Fr E E' e := by
    intro i T σ σ'
    have h1 : e₀.φ (cO.t i) = cA.t i := by
      rw [← htO, ← htA]; exact he₀ _
    change (σ'.hom.φ (e₀.φ (cO.t i)) - σ.hom.φ (e₀.φ (cO.t i)) : T.obj.B) = σ'.hom.φ (cA.t i) - σ.hom.φ (cA.t i)
    rw [h1]
  have fil := _root_.GlobalTheory.CompanionTheory.DPFil.isFil_sFil (TO q l s {V})
  have fil' := _root_.GlobalTheory.CompanionTheory.DPFil.isFil_sFil (TS γ q l s {V})
  obtain ⟨PO, hPO⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {V}
  obtain ⟨PA, hPA⟩ := hPoly γ q (κA O I) l s {V}
  have lem : ∀ (i : ℕ) (a : A), a ∈ pdP γ i → ∀ t : ℤ, (smO γ q l s {V}).LeC a (sFil _ (t - i)) (sFil _ t) :=
    fun i a h t => _root_.GlobalTheory.CompanionTheory.LecShift.leC_shift γ q l s {V} i a h t
  refine hLoc (smO γ q l s {V}) PO PA E E' e he (fun _ => Function.injective_id) S.N S.ν
    (fun i t => sFil _ (t - c - i)) (fun i t => sFil _ (t - i)) (fun t => sFil _ (t - c)) (fun t => sFil _ t) r'
    (fun i => ⟨fun t T => fil.anti (by omega) T, fun t ht => crit_of PO (hPO (t - c - i) (by omega)).1 rfl
        (fun k => by congr 1; ring),
      fun t ht => crit_of PO (hPO (t - i) (by omega)).1 rfl (fun k => by congr 1; ring)⟩)
    ⟨fun t T => fil'.anti (by omega) T, fun t ht => crit_of PA (hPA (t - c) (by omega)).1 rfl (fun k => by congr 1; ring),
      fun t ht => (hPA t (by omega)).1⟩
    (fun i n t => lem i _ (S.mem i n) _) (fun i n t => lem i _ (S.mem i n) _) ?_ j
  intro t _ _
  exact chart_tens γ l s m S q cV cO cA eO eA hD hD' e hiO hiA he₀ c t hc _ _

end GlobalTheory.CompanionTheory.BcLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDvdFactorialMul
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickLine

theorem pow_dvd_factorial_mul {p : ℕ} (hp : p.Prime) (N : ℕ) : p ^ N ∣ (p * N).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem isNilpotent_of_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {p : ℕ} (hp : p.Prime)
    (hn : IsNilpotent (p : A)) {x : A} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨k, hk⟩ := pow_dvd_factorial_mul hp N
  refine ⟨p * N, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hk]
  push_cast
  rw [hN]
  simp

theorem ringHom_eq {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

theorem e_one_mem {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem le_comap_ext {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) :
    J ≤ (Q.ext J).comap (algebraMap B Q.P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

variable (T : Thick (F.cr b ht κ)) (Q : PDPoly T.B) (η₀ : DividedPowers (Q.ext T.J)) (hη : Q.IsStd T.δ η₀)
  (hp : b.p ≠ 0)

def line : Thick (F.cr b ht κ) where
  B := Q.P
  i := (algebraMap T.B Q.P).comp T.i
  J := Q.ext T.J
  δ := η₀
  adm := ⟨fun _ => by simpa using (T.adm.1 hp).map (algebraMap T.B Q.P), fun h => absurd h hp⟩
  compat := IsDPMorphism.comp _ hη.dp T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map
    (CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J))) T.y
  inα := trivial
  w r := by
    change Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)
      ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w r]
    rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

def toLine : T ⟶ line T Q η₀ hη hp where
  φ := algebraMap T.B Q.P
  u j := j.elim
  comm _ := rfl
  dp := hη.dp
  hle := le_comap_ext Q T.J
  pt := rfl
  hx j := j.elim
  hs := by
    rw [s_eq_one T, map_one, mul_one]
    exact (Finset.prod_of_isEmpty (ι := Empty) _).symm
  hv j := j.elim

variable {T Q η₀ hη hp}

theorem exists_ext {T' : Thick (F.cr b ht κ)} (φ : T ⟶ T') {c : T'.B} (hc : c ∈ T'.J) :
    ∃ ψ : line T Q η₀ hη hp ⟶ T', toLine T Q η₀ hη hp ≫ ψ = φ ∧ ψ.φ (Q.e 1) = c := by
  obtain ⟨G, hG1, hG2⟩ := FubiniStudyChowHeightFormula₂.Adr.Fil.exists_lift Q T'.B φ.φ (fun k => T'.δ.dpow k c) (T'.δ.dpow_zero hc) (fun m k => T'.δ.mul_dpow hc)
  have hGa : G.comp (algebraMap T.B Q.P) = φ.φ := RingHom.ext hG1
  have hGdp : IsDPMorphism η₀ T'.δ G :=
    FubiniStudyChowHeightFormula₂.Adr.dp_of_std T.δ Q η₀ hη T'.δ G c hc (by rw [hGa]; exact φ.dp) hG2
  have hle : Q.ext T.J ≤ T'.J.comap G := Ideal.map_le_iff_le_comap.1 hGdp.1
  refine ⟨{ φ := G, u := fun j => j.elim, comm := fun r => ?_, dp := hGdp, hle := hle, pt := ?_,
            hx := fun j => j.elim, hs := ?_, hv := fun j => j.elim }, ?_, ?_⟩
  · exact (hG1 _).trans (φ.comm r)
  · refine Eq.trans ?_ φ.pt
    have e : CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) =
        CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)) ≫
          CommRingCat.ofHom (Ideal.quotientMap T'.J G hle) := by
      refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk T'.J (φ.φ a) = Ideal.Quotient.mk T'.J (G (algebraMap T.B Q.P a))
      rw [hG1]
    rw [e, Functor.map_comp]
    rfl
  · rw [s_eq_one T']
    refine Units.ext ?_
    change (1 : T'.B) = ((∏ j : Empty, (j.elim : T'.Bˣ)) * Units.map G.toMonoidHom 1 : T'.Bˣ)
    simp
  · exact Thick.Hom.ext hGa (funext fun j => j.elim)
  · change G (Q.e 1) = c
    rw [hG2 1]
    exact T'.δ.dpow_one hc

theorem hom_unique {T' : Thick (F.cr b ht κ)} {ψ ψ' : line T Q η₀ hη hp ⟶ T'}
    (h : toLine T Q η₀ hη hp ≫ ψ = toLine T Q η₀ hη hp ≫ ψ') (he : ψ.φ (Q.e 1) = ψ'.φ (Q.e 1)) : ψ = ψ' := by
  refine Thick.Hom.ext (ringHom_eq Q (fun a => ?_) fun k => ?_) (funext fun j => j.elim)
  · exact congrArg (fun f : T ⟶ T' => f.φ a) h
  · have h1 : T'.δ.dpow k (ψ.φ (Q.e 1)) = ψ.φ (η₀.dpow k (Q.e 1)) := ψ.dp.2 (Q.e 1) (e_one_mem Q T.J)
    have h2 : T'.δ.dpow k (ψ'.φ (Q.e 1)) = ψ'.φ (η₀.dpow k (Q.e 1)) := ψ'.dp.2 (Q.e 1) (e_one_mem Q T.J)
    rw [hη.var k] at h1 h2
    have h3 : T'.δ.dpow k (ψ.φ (Q.e 1)) = T'.δ.dpow k (ψ'.φ (Q.e 1)) := congrArg _ he
    exact h1.symm.trans (h3.trans h2)

def lineU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime) :
    (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hpp.ne_zero) :=
  ⟨(isNilpotent_of_mem η₀ hpp (by simpa using (T.adm.1 hpp.ne_zero).map (algebraMap T.B Q.P))
      (e_one_mem Q T.J)).isUnit_one_add.unit,
    MonoidHom.mem_ker.2 (Units.ext (by
      change Ideal.Quotient.mk (Q.ext T.J) (1 + Q.e 1) = Ideal.Quotient.mk (Q.ext T.J) 1
      exact Ideal.Quotient.eq.2 (by simpa using e_one_mem Q T.J)))⟩

theorem map_lineU {T' : Thick (F.cr b ht κ)} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime)
    (ψ : line T Q η₀ hη hpp.ne_zero ⟶ T') :
    ((((thU (F.cr b ht κ) q hq).map ψ (lineU q hq hpp)).1 : T'.Bˣ) : T'.B) = 1 + ψ.φ (Q.e 1) := by
  change (ψ.φ : Q.P →+* T'.B) ((1 : Q.P) + Q.e 1) = 1 + _
  exact (map_add (ψ.φ : Q.P →+* T'.B) 1 (Q.e 1)).trans (by rw [map_one]; rfl)

theorem main : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g := by
  intro O _ F b ht κ Λ _ c ρ hρ μ hμ q hq x hpp hqx hcμ hsum T
  have hp0 := hpp.ne_zero
  obtain ⟨Q⟩ : Nonempty (PDPoly T.B) := ⟨GlobalTheory.PDA.Model.pdPoly T.B⟩
  obtain ⟨η₀, hη⟩ := FubiniStudyChowHeightFormula₂.Adr.exists_std T.B T.J T.δ Q
  refine ⟨line T Q η₀ hη hp0, toLine T Q η₀ hη hp0, lineU q hq hpp, ?_, ?_⟩
  · intro T' φ a
    have hc : ((a.1 : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
      have h : Ideal.Quotient.mk T'.J ((a.1 : T'.Bˣ) : T'.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
      exact Ideal.Quotient.eq.1 (h.trans (map_one _).symm) |> fun h => by simpa using h
    obtain ⟨ψ, h1, h2⟩ := exists_ext (Q := Q) (η₀ := η₀) (hη := hη) (hp := hp0) φ hc
    refine ⟨ψ, ⟨h1, ?_⟩, ?_⟩
    · refine Subtype.ext (Units.ext ?_)
      refine (map_lineU q hq hpp ψ).trans ?_
      rw [h2]
      ring
    · rintro ψ' ⟨h1', h2'⟩
      have e : 1 + ψ'.φ (Q.e 1) = ((a.1 : T'.Bˣ) : T'.B) := (map_lineU q hq hpp ψ').symm.trans
        (congrArg (fun u : (thU (F.cr b ht κ) q hq).U T' => ((u.1 : T'.Bˣ) : T'.B)) h2')
      refine hom_unique (h1'.trans h1.symm) ?_
      rw [h2]
      exact eq_sub_of_add_eq' e
  · intro g hg hgη
    let gφ : Q.P →+* Q.P := g.φ
    have hgφ : gφ.comp (algebraMap T.B Q.P) = algebraMap T.B Q.P :=
      congrArg (fun f : T ⟶ line T Q η₀ hη hp0 => f.φ) hg
    have hmul : gφ (1 + Q.e 1) = algebraMap T.B Q.P ((T.i x) ^ b.p) * (1 + Q.e 1) := by
      have e : gφ (1 + Q.e 1) = algebraMap T.B Q.P (T.i (q : b.R)) * (1 + Q.e 1) :=
        congrArg (fun u : (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hp0) =>
          ((u.1 : (line T Q η₀ hη hp0).Bˣ) : (line T Q η₀ hη hp0).B)) hgη
      rw [e, hqx, map_pow]
    have hsum' : (∑ i ∈ Finset.range b.p, (T.i x) ^ i) ∈ T.J := by
      have := T.i_mem hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_pow] using this
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.PDAcyc.main T.δ Q η₀ hη b.p hpp (T.adm.1 hp0) (T.i x) hsum' gφ hgφ g.dp hmul
    have hμ' : ∀ z : Q.P, algebraMap T.B Q.P ((T.i x) ^ b.p - 1) * z =
        algebraMap T.B Q.P (T.i (c μ)) * z := by
      intro z
      rw [hcμ, hqx, map_sub T.i, map_pow, map_one]
    refine ⟨h1, ?_, ?_⟩
    · intro r z hz hz'
      obtain ⟨m, hm, e⟩ := h2 (ρ r) z hz hz'
      exact ⟨m, T.pdPow_anti (hρ.2 r) hm, e.trans (hμ' z)⟩
    · intro r z hz
      obtain ⟨y, hy, e⟩ := h3 (ρ r) z hz
      exact ⟨y, (line T Q η₀ hη hp0).pdPow_anti (hρ.2 r) hy, e.trans (hμ' z)⟩

end GlobalTheory.CompanionTheory.ThickLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_exists : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper | exact GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pushforward_coherent : ∀ {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → ∀ {G : Z.Modules}, IsCoherent G → IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | exact GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemUnseenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_closed_system_auxiliary : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)), PropSupp A B → PropSupp A (adjKer φ B) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | exact GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_system_killed_by_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData) (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ), (∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U) → ∀ e, Killed J (restrictSys I D S c e) := by
  exact @GlobalTheory.CompanionTheory.GE.killed_restrictSys
end

