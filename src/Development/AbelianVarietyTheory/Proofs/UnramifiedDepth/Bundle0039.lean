module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hs {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (h : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => h q.1 q.2)

private theorem sub_sub' {R : Type} [CommRing R] {m n k d e f : ℕ} (a : Fin m → Fin d → PS R n e)
    (b : Fin n → Fin e → PS R k f) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (u : PS R m d) :
    sub b (sub a u) = sub (fun i j => sub b (a i j)) u :=
  MvPowerSeries.subst_comp_subst_apply (hs a ha) (hs b hb) u

private theorem sub_X {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    sub a (MvPowerSeries.X q) = a q.1 q.2 :=
  MvPowerSeries.subst_X (hs a ha) q

private theorem sub_mul' {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u v : PS R m d) :
    sub a (u * v) = sub a u * sub a v :=
  MvPowerSeries.subst_mul (hs a ha) u v

private theorem const_sub {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u : PS R m d) :
    MvPowerSeries.constantCoeff (sub a u) = MvPowerSeries.constantCoeff u := by
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R R (RingHom.id R) n e 0 (fun _ _ => IsNilpotent.zero)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R R (RingHom.id R) m d 0 (fun _ _ => IsNilpotent.zero)
  have h6 := h6 (by simp)
  have h6' := h6' (by simp)
  have h := h3 m d a u ha
  have e0 : (fun i j => nv (RingHom.id R) (a i j) 0) = 0 := by
    funext i j
    rw [h6, ha]; simp
  rw [e0, h6, h6'] at h
  simpa using h

private theorem coeff_sub {R : Type} [CommRing R] {d e : ℕ} (φ : Fin e → PS R 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (u : PS R 1 e) (k : Fin d) :
    dl (sub ![φ] u) k = ∑ i, lin φ i k * dl u i := by
  classical
  have hφ' : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j; fin_cases i; exact hφ j
  let s : R →+* TrivSqZeroExt R R := algebraMap R _
  let a : Fin 1 → Fin d → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (if j = k then 1 else 0)
  let b : Fin 1 → Fin e → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (lin φ j k)
  have hn : ∀ x : R, IsNilpotent (TrivSqZeroExt.inr x : TrivSqZeroExt R R) := fun x =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R _ s 1 d a (fun _ _ => hn _)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R _ s 1 e b (fun _ _ => hn _)
  have h6 := h6 (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h6' := h6' (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h := h3 1 e ![φ] u hφ'
  have e0 : (fun i j => nv s ((![φ] : Fin 1 → _) i j) a) = b := by
    funext i j
    fin_cases i
    rw [h6, hφ']
    ext
    · have hf : ∀ (t : Finset (Fin 1 × Fin d)) (g : Fin 1 × Fin d → TrivSqZeroExt R R),
          (∑ q ∈ t, g q).fst = ∑ q ∈ t, (g q).fst := fun t g =>
        map_sum (TrivSqZeroExt.fstHom R R R) g t
      simp [s, a, b, hf, apply_ite TrivSqZeroExt.fst]
    · simp [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, lin, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e0, h6, h6'] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simpa [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, TrivSqZeroExt.algebraMap_eq_inl, dl,
    mul_comm] using h2

theorem chain_rule_lin : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  intro R _ d e φ hφ
  have one : ∀ {n f g : ℕ} (x : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![x] : Fin 1 → _) i j) = 0 := by
    intro n f g x hx i j; fin_cases i; exact hx j
  have two : ∀ {n f g : ℕ} (x y : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      (∀ j, MvPowerSeries.constantCoeff (y j) = 0) →
      ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → _) i j) = 0 := by
    intro n f g x y hx hy i j; fin_cases i
    · exact hx j
    · exact hy j
  have hφ' := one φ hφ
  refine ⟨fun u => ⟨?_, const_sub _ hφ' u⟩, fun m ψ => ?_, fun F F' hF u hu => ⟨?_, ?_⟩⟩
  · funext k
    rw [coeff_sub φ hφ u k]
    rfl
  · ext j k
    have := coeff_sub φ hφ (ψ j) k
    rw [Matrix.mul_apply]
    refine this.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · rw [const_sub _ hφ' u, hu.1]
  · have hpt : ∀ (f : ℕ) (i : Fin 2) j, MvPowerSeries.constantCoeff (pt R (n := 2) f i j) = 0 :=
      fun f i j => MvPowerSeries.constantCoeff_X _
    have hid : ∀ (f : ℕ) (G : Fin f → PS R 2 f), addOf G (pt R (n := 2) f 0) (pt R (n := 2) f 1) = G := by
      intro f G
      funext i
      have : (fun p : Fin 2 × Fin f => (![pt R (n := 2) f 0, pt R (n := 2) f 1] : Fin 2 → _) p.1 p.2)
          = MvPowerSeries.X := by
        funext ⟨p, q⟩
        fin_cases p <;> rfl
      simp only [addOf, ev]
      rw [this, MvPowerSeries.subst_self]
      rfl
    have hu2 := hu.2
    rw [hid] at hu2 ⊢
    set x : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 0] (φ i) with hx
    set y : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 1] (φ i) with hy
    have hx0 : ∀ j, MvPowerSeries.constantCoeff (x j) = 0 := fun j => by
      rw [hx]; dsimp only; rw [const_sub _ (one _ (hpt d 0)), hφ]
    have hy0 : ∀ j, MvPowerSeries.constantCoeff (y j) = 0 := fun j => by
      rw [hy]; dsimp only; rw [const_sub _ (one _ (hpt d 1)), hφ]
    have hxy := two x y hx0 hy0
    have h : sub ![x, y] (sub ![F'.F] u) =
        sub ![x, y] (sub ![pt R (n := 2) e 0] u * sub ![pt R (n := 2) e 1] u) := congrArg _ hu2
    rw [sub_mul' _ hxy, sub_sub' _ _ (one _ F'.const) hxy, sub_sub' _ _ (one _ (hpt e 0)) hxy,
      sub_sub' _ _ (one _ (hpt e 1)) hxy] at h
    change sub ![F.F] (sub ![φ] u) =
      sub ![pt R (n := 2) d 0] (sub ![φ] u) * sub ![pt R (n := 2) d 1] (sub ![φ] u)
    rw [sub_sub' _ _ hφ' (one _ F.const), sub_sub' _ _ hφ' (one _ (hpt d 0)),
      sub_sub' _ _ hφ' (one _ (hpt d 1))]
    have e1 : (fun i j => sub ![F.F] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![F'.F] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact hF.2 j
    have e2 : (fun i j => sub ![pt R (n := 2) d 0] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 0] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (0, j)).symm
    have e3 : (fun i j => sub ![pt R (n := 2) d 1] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 1] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (1, j)).symm
    rw [e1, e2, e3]
    exact h

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.ChartBaseChange

theorem isCanonGauge_mapFB {R k : Type} [CommRing R] [Algebra ℚ R] [CommRing k] [Algebra ℚ k]
    (f : R →+* k) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {h : PS R 2 d}
    (hg : B.IsCanonGauge R h) :
    (GlobalTheory.FBMap.mapFB f B).IsCanonGauge k (MvPowerSeries.map f h) := by
  letI : Algebra R k := f.toAlgebra
  have h1 : B.IsCanonGauge k (MvPowerSeries.map f h) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId R k) hg
  have hid : ∀ {σ : Type} (g : MvPowerSeries σ k), MvPowerSeries.map (algebraMap k k) g = g := by
    intro σ g
    ext m
    simp [MvPowerSeries.coeff_map]
  have hF : (GlobalTheory.FBMap.mapFB f B).FK k = B.FK k := funext fun i => hid _
  have hA : ∀ a, (GlobalTheory.FBMap.mapFB f B).actK k a = B.actK k a := fun a => funext fun i => hid _
  refine ⟨h1.ax0, h1.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF, ← h1.ph1]; exact hid _
  · rw [hF, ← h1.ph2]; exact hid _
  · rw [← h1.sy]; exact hid _
  · rw [hA, hA, ← h1.ad a]; exact hid _

theorem intS_map {T : CDVR} {C : Type} [Field C] {V : VF C} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {σ : Type} {g : MvPowerSeries σ T.Fr} {g0 : MvPowerSeries σ T.V}
    (hg : g = MvPowerSeries.map (algebraMap T.V T.Fr) g0) : IntS V (MvPowerSeries.map ι g) := by
  intro m
  rw [hg, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  exact (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1 _

theorem exists_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.BCExSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι hac hcpl hl hw k hk
  obtain ⟨gF, gA, g1, g2, gs, ga, -⟩ := C3.gen.1
  have hg : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    letI := io.toAlgebra
    exact C3.ch.gauge
  obtain ⟨lg, ex, hlin, hadd, hc, hle, hel⟩ :=
    GlobalTheory.FormalLog.exists_log_exp C (chD C3.ch) (GlobalTheory.FBMap.mapFB ι (a3B C3)).G
  exact ⟨{ algClosed := hac
           cpl := hcpl
           l_odd := hl
           B := GlobalTheory.FBMap.mapFB ι (a3B C3)
           h := MvPowerSeries.map ι (a3h C3)
           gauge := isCanonGauge_mapFB ι (a3B C3) hg
           intF := fun i => intS_map hι (gF i)
           intAct := fun a i => intS_map hι (gA a i)
           intPh1 := intS_map hι g1
           intPh2 := intS_map hι g2
           intSy := intS_map hι gs
           intAd := fun a => intS_map hι (ga a)
           lg := lg
           lg_lin := hlin
           lg_add := hadd
           ex := ex
           ex_const := hc
           lg_ex := hle
           ex_lg := hel
           w0 := H.w0
           halfIntegralGenerator_add_conj_eq_one := hw
           k := k
           k_unit := hk },
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩⟩

end GlobalTheory.ChartBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteF
section
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.ChF

namespace GlobalTheory.ChF

private theorem coeff_eq_zero_of_roots {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ]
    [DecidableEq σ] {N : ℕ} {ζ : O} (hζ : IsPrimitiveRoot ζ N) (c : (σ → Fin N) → O)
    (h : ∀ b : σ → ℕ, ∑ a : σ → Fin N, c a * ∏ i, (ζ ^ b i) ^ (a i : ℕ) = 0) : ∀ a, c a = 0 := by
  let χ : (σ → Fin N) → (Multiplicative (σ → ℕ) →* O) := fun a =>
    { toFun := fun b => ∏ i, (ζ ^ (Multiplicative.toAdd b) i) ^ (a i : ℕ)
      map_one' := by simp
      map_mul' := fun b b' => by
        simp [pow_add, mul_pow, Finset.prod_mul_distrib] }
  have hinj : Function.Injective χ := by
    intro a a' haa
    funext j
    have h1 := DFunLike.congr_fun haa (Multiplicative.ofAdd (Pi.single j 1))
    have key : ∀ e : σ → Fin N, χ e (Multiplicative.ofAdd (Pi.single j 1)) = ζ ^ (e j : ℕ) := by
      intro e
      show ∏ i, (ζ ^ (Pi.single j 1 : σ → ℕ) i) ^ (e i : ℕ) = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    rw [key, key] at h1
    exact Fin.ext (hζ.pow_inj (a j).2 (a' j).2 h1)
  have hli := (linearIndependent_monoidHom (Multiplicative (σ → ℕ)) O).comp χ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli c
  funext b
  have := h (Multiplicative.toAdd b)
  simpa [Finset.sum_apply, χ] using this

private theorem map_coe_mem_span {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {σ : Type}
    [Fintype σ] [DecidableEq σ] {N : ℕ} (hN : 0 < N) (ψ : MvPowerSeries σ O →ₐ[O] Q)
    (hy : ∀ i, (1 + ψ (MvPowerSeries.X i)) ^ N = 1) (P : MvPolynomial σ O) :
    ψ (P : MvPowerSeries σ O) ∈ Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) := by
  set S := Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) with hS
  have hmon : ∀ e : σ → ℕ, ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (e i) ∈ S := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % N, Nat.mod_lt _ hN⟩, ?_⟩
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (pow_eq_pow_mod (e i) (hy i)).symm
  have hmul : ∀ j, ∀ q ∈ S, q * (1 + ψ (MvPowerSeries.X j)) ∈ S := by
    intro j q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := hmon (fun i => (a i : ℕ) + (Pi.single j 1 : σ → ℕ) i)
      simp only [pow_add, Finset.prod_mul_distrib] at this
      rwa [Finset.prod_eq_single j (f := fun i =>
        (1 + ψ (MvPowerSeries.X i)) ^ (Pi.single j 1 : σ → ℕ) i)
        (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp), Pi.single_eq_same, pow_one] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact S.smul_mem a hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : Q) ∈ S := by simpa using hmon 0
    have : ψ ((MvPolynomial.C a : MvPolynomial σ O) : MvPowerSeries σ O) = a • (1 : Q) := by
      rw [MvPolynomial.coe_C, ← Algebra.algebraMap_eq_smul_one]
      exact ψ.commutes a
    rw [this]
    exact S.smul_mem a h1
  | add f g hf hg => rw [MvPolynomial.coe_add, map_add (f := _)]; exact S.add_mem hf hg
  | mul_X f j hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]
    have := S.sub_mem (hmul j _ hf) hf
    convert this using 1
    ring

private theorem exists_pow_eq {A : Type} [CommRing A] {p : ℕ} (hp : p.Prime) (k : ℕ) (x : A) :
    ∃ s : A, x ^ p ^ k = ((1 + x) ^ p ^ k - 1) + (p : A) * s := by
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp (1 : A) x k
  refine ⟨-(x * s), ?_⟩
  rw [hs]
  ring

private theorem exists_primitiveRoot_integers {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {N : ℕ}
    (hN : 0 < N) : ∃ ζ : O, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C N
  have hvz : v z ≤ 1 := by
    have : v z ^ N = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hN.ne').1 this).le
  obtain ⟨ζ, rfl⟩ := hv.exists_of_le_one hvz
  exact ⟨ζ, hz.of_map_of_injective hv.hom_inj⟩

theorem fh_gmF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  intro p hp C _ _ _ v O _ _ hv _ hc r k
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain _
  have hN : 0 < p ^ k := pow_pos hp.out.pos k
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_integers hv hN
  have hmul := (gmLaw_chars_mul O r).2.2 (p ^ k)
  set I : Ideal (PS O 1 r) := Ideal.span (Set.range (mulF (gmF O r) (p ^ k))) with hI
  have hrel : ∀ i : Fin 1 × Fin r, (1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1 ∈ I := by
    rintro ⟨i0, i⟩
    obtain rfl : i0 = 0 := Subsingleton.elim _ _
    exact Ideal.subset_span ⟨i, hmul i⟩

  obtain ⟨M, hM⟩ : ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin r → PS O 1 r)) ^ M ≤
      I ⊔ Ideal.map (MvPowerSeries.C : O →+* PS O 1 r) (Ideal.span {(p : O)}) := by
    apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (MvPowerSeries.X i : PS O 1 r)
    refine ⟨p ^ k, ?_⟩
    rw [hs]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (hrel i)) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_))
    rw [← map_natCast (MvPowerSeries.C : O →+* PS O 1 r) p]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  let π : PS O 1 r →ₐ[O] (PS O 1 r ⧸ I) := Ideal.Quotient.mkₐ O I
  let m : (Fin 1 × Fin r → Fin (p ^ k)) → (PS O 1 r ⧸ I) :=
    fun a => ∏ i, (1 + π (MvPowerSeries.X i)) ^ (a i : ℕ)
  have hspan : ∀ q : PS O 1 r ⧸ I, q ∈ Submodule.span O (Set.range m) := by
    intro q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨P, -, hP⟩ := GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O
      (Ideal.span {(p : O)}) (Submodule.fg_span (Set.finite_singleton _)) hc (Fin 1 × Fin r) (Fin r)
      (mulF (gmF O r) (p ^ k)) M hM g
    rw [Ideal.Quotient.eq.2 hP]
    refine map_coe_mem_span hN π (fun i => ?_) P
    have h0 : π ((1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hrel i)
    rw [map_sub, map_pow, map_add (f := _), map_one] at h0
    exact sub_eq_zero.1 h0

  have hpt : ∀ b : Fin 1 × Fin r → ℕ, ∃ φ : (PS O 1 r ⧸ I) →ₐ[O] O,
      ∀ i, φ (π (MvPowerSeries.X i)) = ζ ^ b i - 1 := by
    intro b
    have hone : ∀ i, (1 + (ζ ^ b i - 1)) ^ p ^ k - 1 = 0 := by
      intro i
      rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    obtain ⟨ψ, hψ⟩ := (GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) (Fin 1 × Fin r)
      (fun i => ζ ^ b i - 1) (fun i => by
        obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (ζ ^ b i - 1)
        refine ⟨p ^ k, ?_⟩
        rw [hs, hone, zero_add]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hc O
    have hker : I ≤ RingHom.ker ψ := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show ψ _ = 0
      rw [hmul, map_sub, map_pow, map_add (f := _), map_one, hψ]
      exact hone _
    exact ⟨Ideal.Quotient.liftₐ I ψ (fun a ha => hker ha), fun i => hψ i⟩
  have hsep : ∀ c : (Fin 1 × Fin r → Fin (p ^ k)) → O,
      (∀ φ : (PS O 1 r ⧸ I) →ₐ[O] O, φ (∑ a, c a • m a) = 0) → ∀ a, c a = 0 := by
    intro c hcφ
    refine coeff_eq_zero_of_roots hζ c fun b => ?_
    obtain ⟨φ, hφ⟩ := hpt b
    have := hcφ φ
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul, m, map_prod, map_pow, map_add (f := _), map_one, hφ, add_sub_cancel,
      smul_eq_mul] using this
  have hli : LinearIndependent O m := by
    rw [Fintype.linearIndependent_iff]
    intro c h0
    exact hsep c fun φ => by rw [h0, map_zero]
  let B := Module.Basis.mk hli (fun q _ => hspan q)
  refine ⟨Module.Free.of_basis B, Module.Finite.of_basis B, fun q hq => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hspan q)
  simp [hsep c hq]

end GlobalTheory.ChF
end

