module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm
section
open Polynomial

private theorem charPerm_dvd {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) (ψ : G →* k) : ((ringChar k : ℕ) : ℤ) ∣ f ψ := by
  classical
  have hli := linearIndependent_monoidHom G k
  rw [linearIndependent_iff'] at hli
  have hsum : ∑ φ ∈ f.support, ((f φ : ℤ) : k) • ((φ : G →* k) : G → k) = 0 := by
    funext g
    have h0 := congrArg (fun u : k →₀ ℤ => u.sum (fun v z => (z : k) * v)) (h g)
    simp only [Finsupp.sum_zero_index] at h0
    rw [Finsupp.sum_mapDomain_index (by intro; simp) (by intro _ _ _; push_cast; ring)] at h0
    simpa [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0
  by_cases hψ : ψ ∈ f.support
  · have := hli f.support (fun φ => ((f φ : ℤ) : k)) hsum ψ hψ
    exact (CharP.intCast_eq_zero_iff k (ringChar k) _).mp this
  · have : f ψ = 0 := by simpa using hψ
    rw [this]
    exact dvd_zero _

private theorem charPerm_zero {G k : Type} [Group G] [Field k] (f : (G →* k) →₀ ℤ)
    (h : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) : f = 0 := by
  classical
  by_cases hp : ringChar k = 0
  · ext ψ
    have := charPerm_dvd f h ψ
    rw [hp] at this
    simpa using this
  · have hp1 : 1 < ringChar k :=
      ((CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp).one_lt
    have key : ∀ n : ℕ, ∀ f : (G →* k) →₀ ℤ, (∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f = 0) →
        ∀ ψ, ((ringChar k : ℕ) : ℤ) ^ n ∣ f ψ := by
      intro n
      induction n with
      | zero => intro f _ ψ; simp
      | succ n ih =>
        intro f hf ψ
        let f1 : (G →* k) →₀ ℤ := Finsupp.mapRange (fun z : ℤ => z / ((ringChar k : ℕ) : ℤ)) (by simp) f
        have hf1 : f = ((ringChar k : ℕ) : ℤ) • f1 := by
          ext φ
          simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, f1]
          exact (Int.mul_ediv_cancel' (charPerm_dvd f hf φ)).symm
        have hf1' : ∀ g, Finsupp.mapDomain (fun ψ : G →* k => ψ g) f1 = 0 := by
          intro g
          have := hf g
          rw [hf1, Finsupp.mapDomain_smul] at this
          exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hp)
        have := ih f1 hf1' ψ
        rw [hf1, Finsupp.smul_apply, smul_eq_mul, pow_succ']
        exact mul_dvd_mul_left _ this
    ext ψ
    have hd := key (f ψ).natAbs f h ψ
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    simpa [Int.natAbs_pow] using Nat.lt_pow_self (n := (f ψ).natAbs) hp1

private theorem charPerm_single {α ι : Type} [Fintype ι] (a b : ι → α) :
    Finset.univ.val.map a = Finset.univ.val.map b ↔
      (∑ i, Finsupp.single (a i) (1 : ℤ)) = ∑ i, Finsupp.single (b i) (1 : ℤ) := by
  classical
  have key : ∀ (s : Multiset α) (x : α),
      (s.map (fun y => Finsupp.single y (1 : ℤ))).sum x = (s.count x : ℤ) := by
    intro s x
    induction s using Multiset.induction_on with
    | empty => simp
    | cons y s ih =>
      by_cases hxy : y = x
      · subst hxy
        simp [Multiset.count_cons, ih]
        try ring
      · simp [Multiset.count_cons, ih, Finsupp.single_apply, hxy, Ne.symm hxy]
  have hsum : ∀ c : ι → α, (∑ i, Finsupp.single (c i) (1 : ℤ)) =
      ((Finset.univ.val.map c).map (fun y => Finsupp.single y (1 : ℤ))).sum := by
    intro c
    rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
    rfl
  constructor
  · intro h
    rw [hsum, hsum, h]
  · intro h
    refine Multiset.ext.mpr fun x => ?_
    have := DFunLike.congr_fun h x
    rw [hsum, hsum, key, key] at this
    exact_mod_cast this

private theorem charPerm_perm {α ι : Type} [Fintype ι] (a b : ι → α)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) : ∃ σ : Equiv.Perm ι, ∀ i, b i = a (σ i) := by
  classical
  have hc : ∀ c, Fintype.card {i // b i = c} = Fintype.card {i // a i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_def, Finset.card_def,
      Finset.filter_val, Finset.filter_val]
    have e : ∀ d : ι → α, Multiset.filter (fun x => d x = c) Finset.univ.val =
        Multiset.filter (fun x => c = d x) Finset.univ.val :=
      fun d => Multiset.filter_congr (fun x _ => eq_comm)
    rw [e, e]
    convert this.symm
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

theorem UpperTheory.V.Pr.charPerm :
    UpperTheory.V.Pr.CharPerm := by
  intro G k _ _ n χ χ' hχ
  classical
  let ψ : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ i)
  let ψ' : Fin n → (G →* k) := fun i => (Units.coeHom k).comp (χ' i)
  have hr : ∀ a : Fin n → k, (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
    intro a
    rw [Finset.prod_eq_multiset_prod]
    have : Finset.univ.val.map (fun i => X - C (a i)) = (Finset.univ.val.map a).map (fun x => X - C x) := by
      rw [Multiset.map_map]
      rfl
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : ∀ g, Finset.univ.val.map (fun i => ψ i g) = Finset.univ.val.map (fun i => ψ' i g) := by
    intro g
    have h1 := congrArg Polynomial.roots (hχ g)
    unfold UpperTheory.V.Pr.chPoly at h1
    rw [hr, hr] at h1
    exact h1
  let f : (G →* k) →₀ ℤ := (∑ i, Finsupp.single (ψ' i) (1 : ℤ)) - ∑ i, Finsupp.single (ψ i) 1
  have hf : ∀ g, Finsupp.mapDomain (fun φ : G →* k => φ g) f = 0 := by
    intro g
    simp only [f, Finsupp.mapDomain_sub, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
    rw [sub_eq_zero]
    exact (charPerm_single (fun i => ψ' i g) (fun i => ψ i g)).mp (hroots g).symm
  have hs : (∑ i, Finsupp.single (ψ i) (1 : ℤ)) = ∑ i, Finsupp.single (ψ' i) 1 :=
    (sub_eq_zero.mp (charPerm_zero f hf)).symm
  obtain ⟨σ, hσ⟩ := charPerm_perm ψ ψ' ((charPerm_single ψ ψ').mpr hs)
  refine ⟨σ, fun i => MonoidHom.ext fun g => Units.ext ?_⟩
  exact congrArg (fun φ : G →* k => φ g) (hσ i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CliffPrime
section
open Matrix UpperTheory.V.U3 Module

section

variable {G κ V : Type} [Group G] [Field κ] [AddCommGroup V] [Module κ V]

private theorem hmul (σ : G →* Module.End κ V) (a b : G) (v : V) : σ a (σ b v) = σ (a * b) v := by
  rw [map_mul]; rfl

private theorem hinj (σ : G →* Module.End κ V) (g : G) : Function.Injective (σ g) :=
  Function.LeftInverse.injective (g := σ g⁻¹) fun v => by rw [hmul]; simp

private theorem min_dvd [FiniteDimensional κ V] (σ : G →* Module.End κ V) (U : Subgroup G) [hn : U.Normal]
    (hirr : ∀ W : Submodule κ V, (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule κ V) (hW0 : W ≠ ⊥) (hW : ∀ g ∈ U, ∀ v ∈ W, σ g v ∈ W)
    (hmin : ∀ F : Submodule κ V, F ≠ ⊥ → (∀ g ∈ U, ∀ v ∈ F, σ g v ∈ F) → ¬ F < W) :
    finrank κ W ∣ finrank κ V := by
  obtain ⟨S, ⟨hS, hd⟩, hmax⟩ := (wellFounded_gt (α := Submodule κ V)).has_min
    {F | (∀ g ∈ U, ∀ v ∈ F, σ g v ∈ F) ∧ finrank κ W ∣ finrank κ F} ⟨⊥, by simp +contextual, by simp⟩
  have hle : ∀ g, W ≤ S.comap (σ g) := by
    intro g
    by_contra hg
    have hcom : ∀ h ∈ U, ∀ v ∈ S.comap (σ g), σ h v ∈ S.comap (σ g) := by
      intro h hh v hv
      have := hS (g * h * g⁻¹) (hn.conj_mem h hh g) _ hv
      rw [hmul, inv_mul_cancel_right, ← hmul] at this
      exact this
    have hb : S.comap (σ g) ⊓ W = ⊥ := by
      by_contra hne
      refine hmin _ hne (fun h hh v hv => ⟨hcom h hh v hv.1, hW h hh v hv.2⟩) ?_
      exact lt_of_le_of_ne inf_le_right fun h => hg (inf_eq_right.mp h)
    have hb' : S ⊓ W.map (σ g) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨h1, w, hw, rfl⟩
      have : w ∈ S.comap (σ g) ⊓ W := ⟨h1, hw⟩
      rw [hb, Submodule.mem_bot] at this
      simp [this]
    have hr : finrank κ (W.map (σ g)) = finrank κ W :=
      (Submodule.equivMapOfInjective _ (hinj σ g) W).finrank_eq.symm
    have hs := Submodule.finrank_sup_add_finrank_inf_eq S (W.map (σ g))
    rw [hb', hr, finrank_bot, add_zero] at hs
    refine hmax (S ⊔ W.map (σ g)) ⟨?_, by rw [hs]; exact dvd_add hd dvd_rfl⟩ ?_
    · intro h hh v hv
      obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add (f := _)]
      refine Submodule.add_mem_sup (hS h hh a ha) ⟨_, hW _ (hn.conj_mem' h hh g) b hb, ?_⟩
      rw [hmul, hmul]; congr 2; group
    · refine lt_of_le_of_ne le_sup_left fun h => hg fun w hw => ?_
      rw [Submodule.mem_comap, h]
      exact Submodule.mem_sup_right ⟨w, hw, rfl⟩
  rcases hirr (⨅ g, S.comap (σ g)) (fun g v hv => by
    rw [Submodule.mem_iInf] at hv ⊢
    intro k
    have := hv (k * g)
    rw [Submodule.mem_comap, ← hmul] at this
    exact this) with h | h
  · exact absurd (le_bot_iff.mp (h ▸ le_iInf hle)) hW0
  · have : S = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have : v ∈ ⨅ g, S.comap (σ g) := by rw [h]; trivial
      simpa using (Submodule.mem_iInf _).mp this 1
    rwa [this, finrank_top] at hd

private def eig (σ : G →* Module.End κ V) {U : Subgroup G} (μ : U →* κˣ) : Submodule κ V where
  carrier := {v | ∀ u : U, σ u v = (μ u : κ) • v}
  add_mem' ha hb u := by rw [map_add (f := _), ha u, hb u, smul_add]
  zero_mem' u := by simp
  smul_mem' c a ha u := by rw [map_smul, ha u, smul_comm]

private theorem eig_indep (σ : G →* Module.End κ V) (U : Subgroup G) :
    iSupIndep fun μ : U →* κˣ => eig σ μ := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro v hv h0
    rw [Finset.sum_insert ha] at h0
    have key : ∀ j ∈ s, v j = 0 := by
      intro j hj
      obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp (show j ≠ a from fun h => ha (h ▸ hj))
      have := ih (fun i => ((i u : κ) - a u) • v i)
        (fun i hi => Submodule.smul_mem _ _ (hv i (Finset.mem_insert_of_mem hi))) (by
          have h1 := congrArg (σ u) h0
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_add (f := _), map_sum, map_zero, hv a (Finset.mem_insert_self _ _) u,
            Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi) u] at h1
          simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
          rw [eq_neg_of_add_eq_zero_right h1, eq_neg_of_add_eq_zero_right h0, smul_neg, sub_self]) j hj
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr fun h => hu (Units.ext h))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rwa [Finset.sum_eq_zero key, add_zero] at h0
    · exact key i hi

@[reducible] private def conjAct (U : Subgroup G) [U.Normal] : MulAction G (U →* κˣ) where
  smul g μ := μ.comp (MulAut.conjNormal g⁻¹).toMonoidHom
  one_smul μ := by
    change μ.comp _ = μ
    ext u; simp
  mul_smul a b μ := by
    change μ.comp _ = (μ.comp _).comp _
    ext u; simp

attribute [local instance] conjAct

private theorem eig_smul (σ : G →* Module.End κ V) {U : Subgroup G} [U.Normal] (μ : U →* κˣ) (g : G) {v : V}
    (hv : v ∈ eig σ μ) : σ g v ∈ eig σ (g • μ) := by
  intro u
  have := congrArg (σ g) (hv (MulAut.conjNormal g⁻¹ u))
  rw [map_smul, hmul] at this
  rw [hmul]
  convert this using 3
  · simp [mul_assoc]
  · rfl

private theorem eig_rank [FiniteDimensional κ V] (σ : G →* Module.End κ V) {U : Subgroup G} [U.Normal]
    (μ : U →* κˣ) (g : G) : finrank κ (eig σ (g • μ)) = finrank κ (eig σ μ) := by
  have key : ∀ (μ : U →* κˣ) (g : G), finrank κ (eig σ μ) ≤ finrank κ (eig σ (g • μ)) := fun μ g => by
    rw [(Submodule.equivMapOfInjective _ (hinj σ g) (eig σ μ)).finrank_eq]
    apply Submodule.finrank_mono
    rintro _ ⟨v, hv, rfl⟩
    exact eig_smul σ μ g hv
  refine le_antisymm ?_ (key μ g)
  have := key (g • μ) g⁻¹
  rwa [inv_smul_smul] at this

private theorem of_eig [FiniteDimensional κ V] (σ : G →* Module.End κ V) (U : Subgroup G) [U.Normal]
    (hirr : ∀ W : Submodule κ V, (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤) {n : ℕ} (hp : n.Prime)
    (hn : finrank κ V = n) (μ : U →* κˣ) (hμ : eig σ μ ≠ ⊥) :
    eig σ μ = ⊤ ∨ ∃ (b : Basis (Fin n) κ V) (la : Fin n → U →* κˣ) (π : G →* Equiv.Perm (Fin n)),
      Function.Injective la ∧ (∀ i (u : U), σ u (b i) = ((la i u : κˣ) : κ) • b i) ∧
      (∀ g i, ∃ a : κ, σ g (b i) = a • b (π g i)) ∧ ∀ i j, ∃ g, π g i = j := by
  classical
  let X := MulAction.orbit G μ
  let E : X → Submodule κ V := fun x => eig σ x.1
  have hind : iSupIndep E := (eig_indep σ U).comp Subtype.val_injective
  have hr : ∀ x, finrank κ (E x) = finrank κ (eig σ μ) := by
    rintro ⟨_, g, rfl⟩
    exact eig_rank σ μ g
  have hE0 : ∀ x, E x ≠ ⊥ := fun x h => hμ (by
    rw [← Submodule.finrank_eq_zero, ← hr x, h, finrank_bot])
  have htop : ⨆ x, E x = ⊤ := by
    refine (hirr _ fun g v hv => ?_).resolve_left fun h => hE0 ⟨μ, MulAction.mem_orbit_self μ⟩
      (le_bot_iff.mp (h ▸ le_iSup E _))
    have : ⨆ x, E x ≤ (⨆ x, E x).comap (σ g) := iSup_le fun x w hw =>
      le_iSup E (g • x) (eig_smul σ x.1 g hw)
    exact this hv
  choose b hb hb0 using fun x => Submodule.exists_mem_ne_zero_of_ne_bot (hE0 x)
  have hli : LinearIndependent κ b := hind.linearIndependent E hb hb0
  haveI : Finite X := hli.finite
  haveI : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X * finrank κ (eig σ μ) = n := by
    rw [← hn, ← (LinearEquiv.ofBijective (DirectSum.coeLinearMap E)
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop)).finrank_eq, finrank_directSum]
    simp only [hr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hcard) with h | h
  · right
    rw [h, mul_one] at hcard
    let e : X ≃ Fin n := Fintype.equivFinOfCardEq hcard
    let B : Basis X κ V := Basis.mk hli (htop.ge.trans (iSup_le fun x w hw => by
      obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨b x, hb x⟩ : E x)
        (fun h => hb0 _ (congrArg Subtype.val h))).mp ((hr _).trans h) ⟨w, hw⟩
      have ha' : a • b x = w := congrArg Subtype.val ha
      exact ha' ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)))
    have hB : ∀ i, B.reindex e i = b (e.symm i) := fun i => by simp [B]
    refine ⟨B.reindex e, fun i => (e.symm i).1, e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X),
      Subtype.val_injective.comp e.symm.injective, fun i u => by rw [hB]; exact hb _ u, fun g i => ?_,
      fun i j => ?_⟩
    · have h1 := (finrank_eq_one_iff_of_nonzero' (⟨b (g • e.symm i), hb _⟩ : E (g • e.symm i))
        (fun h => hb0 _ (congrArg Subtype.val h))).mp ((hr _).trans h) ⟨_, eig_smul σ _ g (hb (e.symm i))⟩
      obtain ⟨a, ha⟩ := h1
      refine ⟨a, ?_⟩
      rw [hB, hB]
      simpa using (congrArg Subtype.val ha).symm
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.symm i) (e.symm j)
      exact ⟨g, by simp [hg]⟩
  · exact Or.inl (Submodule.eq_top_of_finrank_eq (h.trans hn.symm))

private theorem exists_eig (σ : G →* Module.End κ V) (U : Subgroup G) (W : Submodule κ V)
    (hW : ∀ g ∈ U, ∀ v ∈ W, σ g v ∈ W) (h1 : finrank κ W = 1) : ∃ μ : U →* κˣ, eig σ μ ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  choose c hc using fun u : U => hv ⟨_, hW u u.2 v v.2⟩
  have hc' : ∀ u : U, σ u v = c u • (v : V) := fun u => (congrArg Subtype.val (hc u)).symm
  have hc0 : ∀ u, c u ≠ 0 := fun u h => hv0' (hinj σ u (by rw [hc', h]; simp))
  refine ⟨MonoidHom.mk' (fun u => Units.mk0 (c u) (hc0 u)) fun a b => Units.ext ?_,
    (Submodule.ne_bot_iff _).mpr ⟨v, hc', hv0'⟩⟩
  refine smul_left_injective κ hv0' ?_
  change c (a * b) • (v : V) = (c a * c b) • (v : V)
  rw [← hc', Subgroup.coe_mul, ← hmul, hc', map_smul, hc', smul_smul, mul_comm]

end

theorem UpperTheory.V.Pr.cliffPrime :
    UpperTheory.V.Pr.CliffPrime := by
  intro G κ _ _ _ n hp r hirr U _
  let σ : G →* Module.End κ (Fin n → κ) :=
    { toFun := fun g => Matrix.toLin' (gm r g)
      map_one' := by simp [gm, Module.End.one_eq_id]
      map_mul' := fun a b => by simp [gm, Matrix.toLin'_mul, Module.End.mul_eq_comp] }
  have hirr' : ∀ W : Submodule κ (Fin n → κ), (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun g _ v hv => hW g v hv
  have hn : finrank κ (Fin n → κ) = n := finrank_fin_fun κ
  haveI : Nontrivial (Fin n → κ) := finrank_pos_iff.mp (hn.symm ▸ hp.pos)
  obtain ⟨W, ⟨hW0, hW⟩, hmin⟩ := (wellFounded_lt (α := Submodule κ (Fin n → κ))).has_min
    {F | F ≠ ⊥ ∧ ∀ g ∈ U, ∀ v ∈ F, σ g v ∈ F} ⟨⊤, top_ne_bot, fun _ _ _ _ => trivial⟩
  have hd := min_dvd σ U hirr' W hW0 hW fun F h1 h2 => hmin F ⟨h1, h2⟩
  rw [hn] at hd
  rcases hp.eq_one_or_self_of_dvd _ hd with h | h
  · obtain ⟨μ, hμ⟩ := exists_eig σ U W hW h
    refine Or.inr ((of_eig σ U hirr' hp hn μ hμ).imp (fun ht u hu => ⟨μ ⟨u, hu⟩, ?_⟩) id)
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have : v ∈ eig σ μ := by rw [ht]; trivial
    simpa [σ] using this ⟨u, hu⟩
  · left
    intro F hF
    have hW' : W = ⊤ := Submodule.eq_top_of_finrank_eq (h.trans hn.symm)
    by_contra hne
    rw [not_or] at hne
    exact hmin F ⟨hne.1, hF⟩ (hW' ▸ lt_top_iff_ne_top.mpr hne.2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CommonFree
section
open scoped Pointwise in
theorem UpperTheory.V.Pr.commonFree :
    UpperTheory.V.Pr.CommonFree := by
  intro H A ι _ _ _ χ N hN htor hex
  classical
  let K : ι → Subgroup H := fun i => ((powMonoidHom N : A →* A).comp (χ i)).ker
  have hK : ∀ i h, h ∈ K i ↔ χ i h ^ N = 1 := fun i h => by
    simp [K, MonoidHom.mem_ker]
  by_contra hno
  push_neg at hno
  have _ : Fintype ι := Fintype.ofFinite ι
  have hcov : ⋃ i ∈ (Finset.univ : Finset ι), (fun _ => (1 : H)) i • ((K i : Set H)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro h
    obtain ⟨i, m, hm, h1⟩ := hno h
    simp only [one_smul, Set.mem_iUnion, Finset.mem_univ, exists_true_left, SetLike.mem_coe, exists_const]
    exact ⟨i, (hK i h).2 (htor i h m hm h1)⟩
  obtain ⟨i, -, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  obtain ⟨h, hh⟩ := hex i
  apply hh
  haveI : (K i).Normal := MonoidHom.normal_ker _
  have hmem := (K i).pow_index_mem h
  rw [hK, map_pow, ← pow_mul] at hmem
  exact htor i h _ (Nat.mul_pos (Nat.pos_of_ne_zero hfin.index_ne_zero) hN) hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfAlg
section
namespace UpperTheory.V.Pr

open IsLocalRing

theorem constOfAlg : ConstOfAlg := by
  intro k A _ _ _ _ _ x c hx hm
  by_contra hne
  have hy : x - algebraMap k A c ≠ 0 := sub_ne_zero.mpr hne
  have hint : IsIntegral k (x - algebraMap k A c) :=
    hx.isIntegral.sub isIntegral_algebraMap
  exact (maximalIdeal.isMaximal A).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hm (hint.isUnit hy))

end UpperTheory.V.Pr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExpSums
section
theorem UpperTheory.V.Pr.expSums :
    UpperTheory.V.Pr.ExpSums := by
  intro κ ι σ _ _ _ α c hα hc
  classical
  by_contra hne
  push Not at hne
  choose C hC using hne
  obtain ⟨a, ha, b, s, hs⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (Fintype.card ι)) C
  let e := (Fintype.equivFin ι).symm
  have hinj : Function.Injective fun j : Fin (Fintype.card ι) => ((α s (e j) : κˣ) : κ) ^ a := by
    intro i j hij
    by_contra h
    refine hα s (e i) (e j) (fun h' => h (e.injective h')) a ha ?_
    apply Units.ext
    simpa using hij
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun j => c s (e j) * ((α s (e j) : κˣ) : κ) ^ b) hinj (by
      intro i
      have h1 := hC (a • (i : ℕ) + b)
      rw [hs i (Finset.mem_range.2 i.2), ← e.sum_comp] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, pow_add, pow_mul]
      ring)
  obtain ⟨i, hi⟩ := hc s
  have h2 := congrFun h0 (e.symm i)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hi h2
  · exact pow_ne_zero _ (α s i).ne_zero h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StrongIrrOfOpen
section
open Matrix

theorem UpperTheory.V.Pr.strongIrrOfOpen :
    UpperTheory.V.Pr.StrongIrrOfOpen := by
  intro G κ _ _ _ _ n r hlin hirr W S hS hiff
  have hset : (S : Set G) = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator,
      {g | φ (UpperTheory.V.Pr.gm r g *ᵥ v) = 0} := by
    ext g
    simp only [SetLike.mem_coe, hiff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (h v hv)
  have hclosed : IsClosed (S : Set G) := by
    rw [hset]
    refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
    let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
      { toFun := fun M => φ (M *ᵥ v)
        map_add' := by
          intro A B
          simp [Matrix.add_mulVec]
        map_smul' := by
          intro c A
          simp [Matrix.smul_mulVec] }
    exact hlin f
  have hopen : IsOpen (S : Set G) := S.isOpen_of_isClosed_of_finiteIndex hclosed
  apply hirr S hopen W
  intro g hg v hv
  exact (hiff g).mp hg v hv
end

