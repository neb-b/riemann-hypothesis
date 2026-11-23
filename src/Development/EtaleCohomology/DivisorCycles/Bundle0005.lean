module

public import Development.EtaleCohomology.DivisorCycles.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.ExpVanPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

theorem deriv_E (Y : Mat C N) (p : Fin N × Fin N) :
    PowerSeries.derivative (R := C) (E Y p) = MvPolynomial.aeval (E Y) (DX Y (MvPolynomial.X p)) := by
  rw [DX, MvPolynomial.mkDerivation_X]
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_derivative, map_sum, map_sum]
  simp only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  have hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹ := by
    have : ((n:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ]; push_cast; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]; ring

omit [CharZero C] in
theorem cc_F (Y : Mat C N) (f : MP C N) : PowerSeries.constantCoeff (F Y f) = ev 1 f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F, ev]
  | add p q hp hq => simp only [F, ev, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *
    rw [hp]; congr 1
    simp [E]

theorem deriv_F (Y : Mat C N) (f : MP C N) :
    PowerSeries.derivative (R := C) (F Y f) = F Y (DX Y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F]
  | add p q hp hq => simp only [F, map_add (f := _)] at * <;> rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add (f := _)] at *
    rw [hp, ← deriv_E]

theorem coeff_F (hT : TanField) (S : Submonoid (Mat C N)) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) :
    ∀ k, ∀ f ∈ Van (S : Set (Mat C N)), PowerSeries.coeff k (F Y f) = 0 := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]
    exact hf 1 S.one_mem
  | succ k ih =>
    intro f hf
    have h := ih _ ((hT C N S Y).1 hY f hf)
    rw [← deriv_F, PowerSeries.coeff_derivative] at h
    have : ((k:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp h).resolve_right this

end LateralTheory.DivDb.ExpVanPf

namespace LateralTheory.DivDb
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.FinDensePf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.FinEmbedPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinEmbedPf

section core
variable {K V U ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup U] [Module K U]

def SS {W : Type} [AddCommGroup W] [Module K W] (a : ι → W →ₗ[K] W) : Prop :=
  ∀ S : Submodule K W, (∀ i, ∀ v ∈ S, a i v ∈ S) → ∃ S' : Submodule K W, IsCompl S S' ∧ ∀ i, ∀ v ∈ S', a i v ∈ S'

def gens (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) : Set (V →ₗ[K] V) :=
  {F | ∃ (t' : U →ₗ[K] V) (t : V →ₗ[K] U), (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧
    F = t' ∘ₗ t}

theorem proj_comm {E : Type} [AddCommGroup E] [Module K E] (p q : Submodule K E) (h : IsCompl p q)
    (φ : E →ₗ[K] E) (hp : ∀ v ∈ p, φ v ∈ p) (hq : ∀ v ∈ q, φ v ∈ q) (x : E) :
    p.projection q h (φ x) = φ (p.projection q h x) := by
  have hx := Submodule.projection_add_projection_eq_self h x
  conv_lhs => rw [← hx]
  rw [map_add (f := _), map_add (f := _), Submodule.projection_apply_of_mem_left h (hp _ (Submodule.projection_apply_mem h x)),
    Submodule.projection_apply_of_mem_right h (hq _ (Submodule.projection_apply_mem h.symm x)), add_zero]

theorem step (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0)
    (E : V →ₗ[K] V) (hE : E ∈ Submodule.span K (gens a b)) (hEi : ∀ x, E (E x) = E x)
    (hEc : ∀ i x, E (a i x) = a i (E x)) (hker : LinearMap.ker E ≠ ⊥) :
    ∃ E' : V →ₗ[K] V, E' ∈ Submodule.span K (gens a b) ∧ (∀ x, E' (E' x) = E' x) ∧
      (∀ i x, E' (a i x) = a i (E' x)) ∧ LinearMap.ker E' < LinearMap.ker E := by
  set P : V →ₗ[K] V := LinearMap.id - E with hPdef
  have hP : ∀ x, P x = x - E x := fun x => rfl
  have hEP : ∀ x, E (P x) = 0 := fun x => by rw [hP, map_sub, hEi, sub_self]
  have hPE : ∀ x, P (E x) = 0 := fun x => by rw [hP, hEi, sub_self]
  have hPP : ∀ x, P (P x) = P x := fun x => by rw [hP (P x), hEP, sub_zero]
  have hPc : ∀ i x, P (a i x) = a i (P x) := fun i x => by rw [hP, hP, hEc, map_sub]
  obtain ⟨t', ht', hPt'⟩ : ∃ t' : U →ₗ[K] V, (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ P ∘ₗ t' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hspan P hcon
    apply hker
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := congrArg (fun f => f m) h0
    simpa [hP, hm] using this
  set M : U →ₗ[K] V := P ∘ₗ t' with hMdef
  have hMc : ∀ i u, a i (M u) = M (b i u) := fun i u => by
    simp only [hMdef, LinearMap.comp_apply]
    rw [← hPc]; congr 1; exact congrArg (fun f => f u) (ht' i)
  have hEM : ∀ u, E (M u) = 0 := fun u => hEP _
  have hPM : ∀ u, P (M u) = M u := fun u => hPP _
  obtain ⟨Cc, hC, hCs⟩ := hU (LinearMap.ker M) (fun i v hv => by
    rw [LinearMap.mem_ker] at hv ⊢; rw [← hMc, hv, map_zero])
  have hinj : ∀ c ∈ Cc, M c = 0 → c = 0 := fun c hc h0 => by
    have : c ∈ LinearMap.ker M ⊓ Cc := ⟨h0, hc⟩
    rw [hC.inf_eq_bot] at this; exact this
  set R : Submodule K V := Submodule.map M Cc with hRdef
  obtain ⟨D, hD, hDs⟩ := hV R (fun i v hv => by
    obtain ⟨c, hc, rfl⟩ := hv
    exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩)
  have hinj' : Function.Injective (M ∘ₗ Cc.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have := hinj (x - y) (Cc.sub_mem x.2 y.2) (by simpa [sub_eq_zero] using hxy)
    exact sub_eq_zero.mp this
  have hRr : LinearMap.range (M ∘ₗ Cc.subtype) = R := by
    ext y; simp [hRdef, Submodule.mem_map]
  let e := LinearEquiv.ofInjective (M ∘ₗ Cc.subtype) hinj'
  let T : V →ₗ[K] U := Cc.subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hRr.symm).toLinearMap ∘ₗ R.projectionOnto D hD
  have hTC : ∀ v, T v ∈ Cc := fun v => (e.symm _).2
  have hMT : ∀ v, M (T v) = R.projection D hD v := fun v => by
    have := congrArg Subtype.val (e.apply_symm_apply
      ((LinearEquiv.ofEq _ _ hRr.symm).toLinearMap (R.projectionOnto D hD v)))
    rw [LinearEquiv.ofInjective_apply] at this
    simpa [T] using this
  have hpc : ∀ i v, R.projection D hD (a i v) = a i (R.projection D hD v) := fun i v =>
    proj_comm R D hD (a i) (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩) (hDs i) v
  have hTc : ∀ i v, T (a i v) = b i (T v) := fun i v => by
    have h1 := hinj (T (a i v) - b i (T v)) (Cc.sub_mem (hTC _) (hCs i _ (hTC v)))
      (by rw [map_sub, hMT, ← hMc, hMT, hpc, sub_self])
    exact sub_eq_zero.mp h1
  set H : V →ₗ[K] V := M ∘ₗ (T ∘ₗ P) with hHdef
  have hH : ∀ x, H x = R.projection D hD (P x) := fun x => hMT _
  have hHgen : H ∈ gens a b := ⟨M, T ∘ₗ P, fun i => LinearMap.ext fun u => by simp [hMc],
    fun i => LinearMap.ext fun v => by simp [hPc, hTc], rfl⟩
  have hprojR : ∀ x, R.projection D hD x ∈ R := fun x => Submodule.projection_apply_mem hD x
  have hER : ∀ y ∈ R, E y = 0 := fun y hy => by
    obtain ⟨c, _, rfl⟩ := hy; exact hEM c
  have hPR : ∀ y ∈ R, P y = y := fun y hy => by rw [hP, hER y hy, sub_zero]
  have hEH : ∀ x, E (H x) = 0 := fun x => by rw [hH]; exact hER _ (hprojR _)
  have hHE : ∀ x, H (E x) = 0 := fun x => by rw [hH, hPE, map_zero]
  have hHH : ∀ x, H (H x) = H x := fun x => by
    rw [hH (H x), hPR _ (by rw [hH]; exact hprojR _), hH,
      Submodule.projection_apply_of_mem_left hD (hprojR _)]
  refine ⟨E + H, Submodule.add_mem _ hE (Submodule.subset_span hHgen), fun x => ?_, fun i x => ?_, ?_⟩
  · simp only [LinearMap.add_apply, map_add (f := _), hEi, hEH, hHE, hHH, add_zero, zero_add]
  · simp only [LinearMap.add_apply, map_add (f := _), hEc, hH, hPc, hpc]
  · have hle : LinearMap.ker (E + H) ≤ LinearMap.ker E := fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.add_apply] at hx
      have := congrArg E hx
      rw [map_add (f := _), hEi, hEH, add_zero, map_zero] at this
      exact this
    refine lt_of_le_of_ne hle (fun heq => ?_)
    have hRne : ∃ c ∈ Cc, M c ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hPt'
      ext u
      have hu : u ∈ LinearMap.ker M ⊔ Cc := by rw [hC.sup_eq_top]; trivial
      obtain ⟨k, hk, c, hc', rfl⟩ := Submodule.mem_sup.mp hu
      show M (k + c) = 0
      rw [map_add (f := _), LinearMap.mem_ker.mp hk, hc c hc', add_zero]
    obtain ⟨c, hc, hne⟩ := hRne
    have hyR : M c ∈ R := ⟨c, hc, rfl⟩
    have hy : M c ∈ LinearMap.ker E := hEM c
    rw [← heq, LinearMap.mem_ker, LinearMap.add_apply, hEM, zero_add, hH, hPR _ hyR,
      Submodule.projection_apply_of_mem_left hD hyR] at hy
    exact hne hy

theorem main (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0) :
    (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
  have key : ∀ d : ℕ, ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
      (∀ i x, E (a i x) = a i (E x)) → Module.finrank K (LinearMap.ker E) ≤ d →
      (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
    have fin : ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
        LinearMap.ker E = ⊥ → (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
      intro E hE hi hk
      have : E = LinearMap.id := by
        ext x
        have h1 : E (E x - x) = 0 := by rw [map_sub, hi, sub_self]
        have := (LinearMap.ker_eq_bot'.mp hk) _ h1
        simpa [sub_eq_zero] using this
      rw [← this]; exact hE
    intro d
    induction d with
    | zero =>
      intro E hE hi _ hd
      exact fin E hE hi (Submodule.finrank_eq_zero.mp (by omega))
    | succ d ih =>
      intro E hE hi hc hd
      by_cases hk : LinearMap.ker E = ⊥
      · exact fin E hE hi hk
      · obtain ⟨E', hE', hi', hc', hlt⟩ := step a b hV hU hspan E hE hi hc hk
        have := Submodule.finrank_lt_finrank_of_lt hlt
        exact ih E' hE' hi' hc' (by omega)
  exact key _ 0 (Submodule.zero_mem _) (fun x => by simp) (fun i x => by simp)
    (Submodule.finrank_le _)

end core

theorem FinEmbed_of : FinEmbed := by
  intro Γ K _ _ N n ρ r A B hSub hρ hr
  let a : Γ → (Fin N → K) →ₗ[K] (Fin N → K) := fun g => Matrix.toLin' (ρ g : Mat K N)
  let b : Γ → (Fin n → K) →ₗ[K] (Fin n → K) := fun g => Matrix.toLin' (r g : Mat K n)
  have hV : SS a := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hρ S (fun g v hv => by simpa [a, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [a, Matrix.toLin'_apply] using h2 g v hv⟩
  have hU : SS b := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hr S (fun g v hv => by simpa [b, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [b, Matrix.toLin'_apply] using h2 g v hv⟩
  have hspan : ∀ Z : (Fin N → K) →ₗ[K] (Fin N → K),
      (∀ t : (Fin n → K) →ₗ[K] (Fin N → K), (∀ g, a g ∘ₗ t = t ∘ₗ b g) → Z ∘ₗ t = 0) → Z = 0 := by
    intro Z hZ
    have h0 := hSub.2.2 (LinearMap.toMatrix' Z) (fun T hT => by
      have := hZ (Matrix.toLin' T) (fun g => by
        simp only [a, b, ← Matrix.toLin'_mul, hT g])
      have := congrArg LinearMap.toMatrix' this
      simpa [LinearMap.toMatrix'_comp] using this)
    have := congrArg Matrix.toLin' h0
    simpa using this
  have hid := main a b hV hU hspan
  obtain ⟨k, f, g, hsum⟩ := Submodule.mem_span_set'.mp hid
  have hg : ∀ j, ∃ (t' : (Fin n → K) →ₗ[K] (Fin N → K)) (t : (Fin N → K) →ₗ[K] (Fin n → K)),
      (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧ (g j : _) = t' ∘ₗ t := fun j => (g j).2
  choose t' t ht' ht hEq using hg
  refine ⟨k, fun j => LinearMap.toMatrix' (t j), fun j => f j • LinearMap.toMatrix' (t' j), ?_, ?_, ?_⟩
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht j g)
    simpa [a, b, LinearMap.toMatrix'_comp] using this
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht' j g)
    simp only [a, b, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at this
    rw [Matrix.mul_smul, smul_mul, this]
  · have h1 : ∑ j, f j • (t' j ∘ₗ t j) = LinearMap.id := by
      rw [← hsum]; exact Finset.sum_congr rfl fun j _ => by rw [hEq]
    have h2 := congrArg LinearMap.toMatrix' h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.toMatrix'_id] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, LinearMap.toMatrix'_comp, smul_mul]

end LateralTheory.DivDb.FinEmbedPf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.FinPolyPf
section
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinPolyPf

variable {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}

omit [IsAlgClosed K] in
theorem root_sub (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hP : P ≠ 0) (hx : aeval x P = 0) :
    x.charpoly.roots ⊆ P.roots := by
  intro a ha
  rw [Polynomial.mem_roots (Matrix.charpoly_monic x).ne_zero] at ha
  rw [Polynomial.mem_roots hP]
  cases n with
  | zero => simp [Matrix.charpoly, Matrix.det_fin_zero] at ha
  | succ m =>
    have hs : a ∈ spectrum K x := Matrix.mem_spectrum_of_isRoot_charpoly ha
    have h2 := spectrum.subset_polynomial_aeval x P ⟨a, hs, rfl⟩
    rw [hx, spectrum.zero_eq] at h2
    simpa using h2

theorem card_roots_eq (P : K[X]) : Multiset.card P.roots = P.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

theorem cp_card (x : Matrix (Fin n) (Fin n) K) : Multiset.card x.charpoly.roots = n := by
  rw [card_roots_eq, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem eq_of_roots (x : Matrix (Fin n) (Fin n) K) (P : K[X]) (hm : P.Monic)
    (h : x.charpoly.roots = P.roots) : x.charpoly = P := by
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic x) (card_roots_eq _),
    ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (card_roots_eq _), h]

theorem FinPoly_of : FinPoly := by
  intro K _ _ n x P hm hd hx
  have hsub := root_sub x P hm.ne_zero hx
  have hPc : Multiset.card P.roots = n := by rw [card_roots_eq, hd]
  refine ⟨fun hsep => ?_, fun hpg hdet => ?_⟩
  · apply eq_of_roots x P hm
    have hle : x.charpoly.roots ≤ P.roots :=
      (Multiset.le_iff_subset (Polynomial.nodup_roots hsep)).2 hsub
    exact Multiset.eq_of_le_of_card_le hle (by rw [hPc, cp_card])
  · apply eq_of_roots x P hm
    by_contra hne
    refine hpg.2 _ (fun a ha => hsub ha) (cp_card x) hne ?_
    rw [← Matrix.det_eq_prod_roots_charpoly, hdet,
      (IsAlgClosed.splits P).coeff_zero_eq_prod_roots_of_monic hm, hd, ← mul_assoc, ← pow_add,
      Even.neg_one_pow ⟨n, rfl⟩, one_mul]

end LateralTheory.DivDb.FinPolyPf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.FinSubOf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FiniteSubrepresentation

variable {K : Type} [Field K] {N n : ℕ}

theorem pow_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (k : ℕ) : X ^ k * T = T * Y ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem aeval_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (q : Polynomial K) : Polynomial.aeval X q * T = T * Polynomial.aeval Y q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, pow_tw X Y T h]

end LateralTheory.DivDb.FiniteSubrepresentation

theorem LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of : LateralTheory.DivDb.FinSub := by
  intro Γ K _ _ N n ρ r A B hS hρ
  obtain ⟨hBA, hAr, hspan⟩ := hS
  have hinj : ∀ w : Fin n → K, A *ᵥ w = 0 → w = 0 := by
    intro w hw
    have := congrArg (B *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, hBA] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨W'', hc, hs⟩ := hρ (W.map (Matrix.mulVecLin A)) (by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨(r g : Matrix (Fin n) (Fin n) K) *ᵥ w, hW g w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAr g])
    refine ⟨W''.comap (Matrix.mulVecLin A), ?_, ?_⟩
    · constructor
      · rw [Submodule.disjoint_def]
        intro w hw hw'
        apply hinj
        have h1 : A *ᵥ w ∈ W.map (Matrix.mulVecLin A) := ⟨w, hw, rfl⟩
        exact (Submodule.disjoint_def.mp hc.disjoint) _ h1 hw'
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        have hv : A *ᵥ v ∈ W.map (Matrix.mulVecLin A) ⊔ W'' := by rw [hc.sup_eq_top]; trivial
        obtain ⟨y, ⟨w, hw, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
        rw [Submodule.mem_sup]
        refine ⟨w, hw, v - w, ?_, by abel⟩
        show A *ᵥ (v - w) ∈ W''
        rw [Matrix.mulVec_sub, ← hyz]
        simpa [Matrix.mulVecLin_apply] using hz
    · intro g v hv
      show A *ᵥ ((r g : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ W''
      rw [Matrix.mulVec_mulVec, ← hAr g, ← Matrix.mulVec_mulVec]
      exact hs g _ hv
  · apply le_antisymm
    · simpa using Matrix.rank_le_width A
    · have := Matrix.rank_mul_le_right B A
      rw [hBA, Matrix.rank_one] at this
      simpa using this
  · intro g
    rw [Matrix.mul_assoc, hAr g, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · intro g q
    constructor
    · intro h
      have h2 := aeval_tw _ _ A (hAr g) q
      rw [h, Matrix.zero_mul] at h2
      have h3 := congrArg (B * ·) h2
      simpa [← Matrix.mul_assoc, hBA] using h3.symm
    · intro h
      apply hspan
      intro T hT
      rw [aeval_tw _ _ T (hT g) q, h, Matrix.mul_zero]
end

-- bundled from Development.EtaleCohomology.DivisorCycles.StructPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
end

