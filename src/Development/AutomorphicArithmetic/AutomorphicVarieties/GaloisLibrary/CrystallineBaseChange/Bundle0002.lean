module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
public import Mathlib.NumberTheory.LSeries.PrimesInAP

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
section
open NumberField

private theorem quadFam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) := by
  obtain ⟨K, hF, hN, hr, hd⟩ := KStar.Consta.exists_quadField hp h4
  have hp0 : p ≠ 0 := hp.ne_zero
  have htc : IsTotallyComplex K :=
    (KStar.Choice.exists_sq_eq_neg_of_discr hr hp0 hd).2
  have hq : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hr }
  exact ⟨K, hF, hN, IsCMField.ofCMExtension ℚ K, hr, hd⟩

theorem UpperTheory.V.Br.quadFam :
    UpperTheory.V.Br.QuadFam := by
  intro N
  have hS : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨p, hpn, hpp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 3) (by norm_num) (by norm_num)
    exact ⟨p, ⟨hpp, hmod⟩, hpn⟩
  let e := hS.natEmbedding
  let q : Fin N → ℕ := fun i => (e i.val).1
  have hq : ∀ i, (q i).Prime ∧ q i % 4 = 3 := fun i => (e i.val).2
  have hinj : ∀ i j, q i = q j → i = j := fun i j h =>
    Fin.ext (e.injective (Subtype.ext h))
  choose K hF hN hC hr hd using fun i => quadFam_one (q i) (hq i).1 (hq i).2
  refine ⟨K, hF, hN, hC, hr, ?_⟩
  intro i j hij
  rw [hd i, hd j]
  have hne : q i ≠ q j := fun h => hij (hinj i j h)
  have hcop : Nat.Coprime (q i) (q j) := (Nat.coprime_primes (hq i).1 (hq j).1).2 hne
  exact (Nat.isCoprime_iff_coprime.2 hcop).neg_neg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
section
open UpperTheory.V UpperTheory.V.Af

private theorem schur_scalar_of_commutes_irreducible {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : Matrix (Fin n) (Fin n) k)
    (hg : ∀ s, g * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * g) :
    ∃ c : k, g = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨hne, -, hmin⟩ := hirr
  have hnt : Nontrivial (Fin n → k) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))
  refine ⟨c, ?_⟩
  rcases hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by
      intro t v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c := by
      rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]; simp

private theorem part_two {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r r' : Γ →* GL (Fin n) k)
    (hirr : IsIrr (r.comp φ)) (hiso : RepIso (r.comp φ) (r'.comp φ)) : RepIso r r' ∨ RepIso (tw r δ) r' := by
  obtain ⟨g, hg⟩ := hiso
  have hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹ := by
    intro s hs
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hg x
  by_cases hall : ∀ s, δ s = 1
  · exact Or.inl ⟨g, fun s => hH s (hall s)⟩
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g := ⟨_, rfl⟩
  have hrt : r' t = g * (r t * u) * g⁻¹ := by rw [hu]; group
  have hcomm : ∀ s, δ s = 1 → u * r s = r s * u := by
    intro s hs
    have e1 := hH s hs
    have e2 := hH (t * s * t⁻¹) (by simp [hs])
    simp only [map_mul, map_inv] at e2
    rw [e1, hrt] at e2
    have e3 : u * r s = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u := by
      group
    rw [e3, e2]; group
  obtain ⟨c, hc⟩ := schur_scalar_of_commutes_irreducible (r.comp φ) hirr (u : Matrix (Fin n) (Fin n) k) (by
    intro x
    have := hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)
    simpa using congrArg Units.val this)
  have hcen : ∀ a : GL (Fin n) k, u * a = a * u := by
    intro a
    apply Units.ext
    simp [hc]
  have huu : u * u = 1 := by
    have e2 := hH (t * t) (by simp [ht'])
    simp only [map_mul] at e2
    rw [hrt] at e2
    have e3 : u * r t * u = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g := by group
    rw [e2, hcen (r t)] at e3
    calc u * u = (r t)⁻¹ * (r t * u * u) := by group
      _ = 1 := by rw [e3]; group
  have hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹ := by
    intro s hs
    have e1 := hH (t⁻¹ * s) (by simp [hs, ht'])
    have e2 : r' s = r' t * r' (t⁻¹ * s) := by rw [← map_mul]; simp
    rw [e2, e1, hrt, ← hcen (r t), map_mul, map_inv]; group
  have hu2 : u = 1 ∨ u = -1 := by
    have e := congrArg Units.val huu
    rw [Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one] at e
    have hn : Nonempty (Fin n) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hirr.1 (Subsingleton.elim _ _)
    obtain ⟨i⟩ := hn
    have e' := congrFun (congrFun e i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'
    rcases mul_self_eq_one_iff.1 e' with h | h
    · left; apply Units.ext; simp [hc, h]
    · right; apply Units.ext; simp [hc, h]
  rcases hu2 with h | h
  · refine Or.inl ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · exact hH s hs
    · rw [hneg s hs, h, one_mul]
  · refine Or.inr ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · rw [hH s hs]; congr 2; apply Units.ext; simp [tw_val, hs]
    · rw [hneg s hs, h]; congr 2; apply Units.ext; simp [tw_val, hs]

private theorem part_one {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (hn : ¬ RepIso r (tw r δ)) : IsIrr (r.comp φ) := by
  refine ⟨hirr.1, fun _ _ _ => trivial, ?_⟩
  intro W _ hW
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  apply hn
  by_cases hall : ∀ s, δ s = 1
  · refine ⟨1, fun s => ?_⟩
    apply Units.ext; simp [tw_val, hall s]
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)
  have hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v
    simp [ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  have a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W := by
    intro s hs v hv
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hW x v hv
  have a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t) := by
    intro s hs v hv
    refine ⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩
    rw [hmul]; simp
  have a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t) := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a2 _ (by simp [hs, ht']) v hv
  have a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a1 _ (by simp [hs, ht']) v hv
  have hinf : W ⊓ W.map (ρ t) = ⊥ := by
    refine (hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))
    intro s v hv
    rcases h2 s with hs | hs
    · exact ⟨a1 s hs v hv.1, a3 s hs v hv.2⟩
    · exact ⟨a4 s hs v hv.2, a2 s hs v hv.1⟩
  have hsup : W ⊔ W.map (ρ t) = ⊤ := by
    refine (hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))
    intro s v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show ρ s (a + b) ∈ _
    rw [map_add (f := _)]
    rcases h2 s with hs | hs
    · exact Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)
    · rw [add_comm]; exact Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)
  have hc : IsCompl W (W.map (ρ t)) := IsCompl.of_eq hinf hsup
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)
  have p1 : ∀ v ∈ W, P v = v := fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)
  have p2 : ∀ v ∈ W.map (ρ t), P v = -v := fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)
  have hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v := fun v =>
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hPP : P ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    simp [p1 a ha, p2 b hb]
  have hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s := by
    intro s
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rcases h2 s with hs | hs
    · simp [p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]
    · simp [p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]
  have hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have := congrArg LinearMap.toMatrix' (hPr s)
  simp only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this
  simp only [Units.val_mul, tw_val, Matrix.smul_mul]
  exact this

theorem UpperTheory.V.Br.resTwo :
    UpperTheory.V.Br.ResTwo := by
  intro Γ Γ' k _ _ _ _ _ n φ δ h1 h2 r
  exact ⟨part_one φ δ h1 h2 r, fun r' => part_two φ δ h1 h2 r r'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RootSum
section
open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem roots_finset (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    ∃ T : Finset (Multiset ℂ), T.card ≤ 2 ^ B.card ∧ ∀ C : Multiset ℂ, C.map (· ^ f) = B → C ∈ T := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
    refine ⟨{0}, by simp, fun C hC => ?_⟩
    simpa using hC
  | cons b B ih =>
    obtain ⟨T, hT, hm⟩ := ih
    refine ⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Multiset.card_cons, pow_succ']
      exact Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT
    · obtain ⟨a, ha, hab, hr⟩ := (Multiset.map_eq_cons _ _ _ _).2 hC
      refine Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)

private theorem roots_card (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    Finite {C : Multiset ℂ // C.map (· ^ f) = B} ∧ Nat.card {C : Multiset ℂ // C.map (· ^ f) = B} ≤ 2 ^ B.card := by
  obtain ⟨T, hT, hm⟩ := roots_finset f h1 h2 B
  let g : {C : Multiset ℂ // C.map (· ^ f) = B} → T := fun C => ⟨C.1, hm _ C.2⟩
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  refine ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩
  simpa using hT

private theorem pairs_card {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) :
    Finite {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ∧
      Nat.card {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≤ 2 ^ n * Nat.card D.S := by
  haveI := D.fin
  haveI := Fintype.ofFinite D.S
  haveI : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1
  let e := Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_
  · have := (roots_card f h1 h2 (D.β s)).2
    rwa [D.card] at this
  · simp [mul_comm]

private theorem pairs_conj {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ e : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≃ {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1},
      ∀ x, (e x).1.2 = x.1.2.map σ := by
  haveI := (pairs_card D f h1 h2).1
  obtain ⟨e, he⟩ := D.conj σ
  let g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} → {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} :=
    fun x => ⟨(e x.1.1, x.1.2.map σ), by
      show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)
      rw [he, ← x.2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp⟩
  have hg : Function.Injective g := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩

private theorem int_root (p f : ℕ) (h1 : 1 ≤ f) (a : ℤ) (b : ℂ) (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) :
    IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  refine IsIntegral.of_pow (n := f) h1 ?_
  convert h using 1
  rw [mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.rootSum :
    UpperTheory.V.Br.RootSum := by
  intro n p hp m wt I _ q f hf D
  haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} :=
    fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1
  have hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), ∀ b ∈ x.1.2,
      b ^ f i ∈ (D i).β x.1.1 := fun i x b hb => by
    rw [← x.2]
    exact Multiset.mem_map_of_mem _ hb
  refine ⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance,
    fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · rintro ⟨i, x, t⟩
    have := (D i).card x.1.1
    rw [← x.2, Multiset.card_map] at this
    exact this
  · intro σ
    choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ
    exact ⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩
  · rintro ⟨i, x, t⟩ b hb
    have h := (D i).pure _ _ (hmem i x b hb)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i := by rw [(hf i).2.2, Nat.cast_pow]
    rw [norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0, Real.rpow_natCast] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).int a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b ?_
    rw [← (hf i).2.2]
    exact h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).intInv a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b⁻¹ ?_
    rw [← (hf i).2.2, inv_pow]
    exact h
  · show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _
    rw [Nat.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have := (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2
    calc _ ≤ 2 ^ n * Nat.card (D i).S * 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
section
open NumberField UpperTheory.V.Af.Bc

private theorem range_res_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

private theorem equiv_of_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω] (K K' : Type) [Field K] [Algebra F K]
    [Algebra K Ω] [IsScalarTower F K Ω] [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

theorem UpperTheory.V.Br.signNe :
    UpperTheory.V.Br.SignNe := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq
  obtain ⟨e⟩ := equiv_of_range K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at this <;> norm_num at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
section
open UpperTheory.V.Af

theorem UpperTheory.V.Br.twCard :
    UpperTheory.V.Br.TwCard := by
  intro Γ k _ _ n r hirr S hS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Submodule.eq_bot_of_subsingleton) hirr.1
    · exact h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose! g hg using hS
  have key : ∀ δ ∈ S, ∀ s, ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = ((δ s : kˣ) : k) • ((r s : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k)) := by
    intro δ hδ s
    have h1 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k))
      (hg δ hδ s)
    simp only [tw_val, Units.val_mul, mul_assoc, Units.inv_mul, mul_one] at h1
    rw [← h1, smul_mul_assoc]
  have hli : LinearIndependent k (fun δ : S => ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc δ0
    have hsum : ∀ s, ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      intro s
      have h2 : (r s : Matrix (Fin n) (Fin n) k) *
          ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
        rw [Finset.mul_sum]
        have e : ∑ δ : S, (r s : Matrix (Fin n) (Fin n) k) *
            ((c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
            (∑ δ : S, c δ • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) * (r s : Matrix (Fin n) (Fin n) k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun δ _ => ?_
          rw [smul_mul_assoc, key δ.1 δ.2 s, mul_smul_comm, mul_smul]
        rw [e, hc, zero_mul]
      have h3 := congrArg (fun A => (((r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A) h2
      simpa [← mul_assoc] using h3
    have hD := (linearIndependent_monoidHom Γ k).comp (fun δ : S => (Units.coeHom k).comp δ.1)
      (fun a b hab => Subtype.ext (MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun hab s)))
    rw [Fintype.linearIndependent_iff] at hD
    have hz : ∀ i j, ∀ δ : S, c δ * ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j
      apply hD
      funext s
      have e := congrFun (congrFun (hsum s) i) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, MonoidHom.coe_comp,
        Units.coeHom_apply, Pi.zero_apply]
      rw [← e]
      exact Finset.sum_congr rfl fun δ _ => by ring
    by_contra hc0
    have h0 : ((g δ0 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      ext i j
      exact (mul_eq_zero.mp (hz i j δ0)).resolve_left hc0
    exact (g δ0).ne_zero h0
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, Fintype.card_coe] at hcard
  rw [sq]
  exact hcard
end

