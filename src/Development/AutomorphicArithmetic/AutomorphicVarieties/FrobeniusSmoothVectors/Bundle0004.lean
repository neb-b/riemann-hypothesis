module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgClosed
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_closed :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ c : ℕ → C, (∀ N, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1)) → ∃ x : C, ∀ N, algebraMap C D (x - c N) ∈ 𝔪 ^ (N + 1) := by
  intro C _ _ _ _ D _ _ 𝔪 h c hc
  let J : ℕ → Ideal C := fun n => (𝔪 ^ n).comap (algebraMap C D)
  have hJ : Antitone J := fun _ _ hab => Ideal.comap_mono (Ideal.pow_le_pow_right hab)
  have h0 : ⨅ n, J n = ⊥ := by
    simp only [J]
    rw [← Ideal.comap_iInf, h.sep, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
    exact h.inj
  choose s hs using GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot J hJ h0
  have hd : ∀ N d, c (N + d) - c N ∈ J (N + 1) := fun N d => by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : c (N + d + 1) - c (N + d) ∈ J (N + 1) := hJ (show N + 1 ≤ N + d + 1 by omega) (hc (N + d))
      have := (J (N + 1)).add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  have hle : ∀ {a b}, a ≤ b → c b - c a ∈ J (a + 1) := fun {a b} hab => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact hd a d
  let t : ℕ → ℕ := fun k => k + ∑ i ∈ Finset.range (k + 1), s i
  have ht : ∀ k, s k ≤ t k := fun k => by
    simp only [t, Finset.sum_range_succ]
    omega
  have ht' : ∀ k, k ≤ t k := fun k => Nat.le_add_right _ _
  have htm : Monotone t := fun a b hab =>
    Nat.add_le_add hab (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal C) (fun k => c (t k)) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact hs m (hJ (by have := ht m; omega) (hle (htm hmn)))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun N => ?_⟩
  have h1 : c (t (N + 1)) - L ∈ J (N + 1) := by
    have := hL (N + 1)
    rw [← h.comap] at this
    exact Ideal.le_comap_pow _ (N + 1) this
  have h2 : c (t (N + 1)) - c N ∈ J (N + 1) := hle (by have := ht' (N + 1); omega)
  have h3 := (J (N + 1)).sub_mem h2 h1
  rwa [sub_sub_sub_cancel_left] at h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgCont
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem locConst_of_factor {X Y Z : Type} [TopologicalSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (h : X → Z) (H : ∀ x y, f x = f y → h x = h y) : IsLocallyConstant h := by
  intro s
  have e : h ⁻¹' s = f ⁻¹' (f '' (h ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      show h x ∈ s
      rw [← H y x hyx]
      exact hy
  rw [e]
  exact hf _

private theorem algebraMap_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : algebraMap C (lauSub P) c ∈ vertex (P := P) h ^ N := by
  have hle : Ideal.map (algebraMap C (lauSub P)) (maximalIdeal C) ≤ vertex (P := P) h := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap]
    change ∃ a ∈ maximalIdeal C,
      algebraMap C K a = ((algebraMap C (lauSub P) c : lauSub P).1).coeff 0
    refine ⟨c, hc, ?_⟩
    show _ = (AddMonoidAlgebra.single 0 (algebraMap C K c)).coeff 0
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hm := Ideal.mem_map_of_mem (algebraMap C (lauSub P)) hc
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle N hm

private theorem single_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (d : ℤ) (M : Submodule C K)
    (hM : M ≤ P d) {x : K} (hx : x ∈ maximalIdeal C ^ N • M) :
    ∃ p ∈ vertex (P := P) h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d x := by
  refine Submodule.smul_induction_on
    (p := fun y => ∃ p ∈ vertex (P := P) h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d y) hx ?_ ?_
  · intro c hc m hm
    refine ⟨algebraMap C (lauSub P) c * ⟨AddMonoidAlgebra.single d m, single_mem_lauSub P (hM hm)⟩,
      Ideal.mul_mem_right _ _ (algebraMap_mem_vertex_pow h N hc), ?_⟩
    rw [Subalgebra.coe_mul]
    show AddMonoidAlgebra.single 0 (algebraMap C K c) * AddMonoidAlgebra.single d m = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, Algebra.smul_def]
  · rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    exact ⟨p + q, add_mem hp hq, by rw [Subalgebra.coe_add, hpx, hqy, AddMonoidAlgebra.single_add]⟩

theorem UpperTheory.V.Fr.alg_cont :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → ρD.Cont (vertex (P := ρ.part C) h) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  refine ⟨fun i j N => ?_, fun v i N => ?_⟩
  · refine locConst_of_factor (hc.cont i j N) _ fun g g' hgg => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hgg
    have hS : Submodule.span C (Set.range fun g => ρ.r g i j) ≤ ρ.part C (w n i - w n j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g0, rfl⟩
      exact NRep.r_mem_part C ρ g0 i j
    obtain ⟨p, hp, hpe⟩ := single_mem_vertex_pow h N (w n i - w n j) _ hS hgg
    rw [Ideal.Quotient.eq]
    have e : ρD.r g i j - ρD.r g' i j = p := by
      apply Subtype.ext
      rw [hpe, AddSubgroupClass.coe_sub, hr, hr, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hp
  · obtain ⟨χ, hχ, hχe⟩ := hc.psi
    refine locConst_of_factor ((hχ v i).1 N) _ fun g g' hgg => ?_
    rw [Ideal.Quotient.eq] at hgg ⊢
    have hm := algebraMap_mem_vertex_pow h N hgg
    have e : (↑(ρD.ψ v i g) : lauSub (ρ.part C)) - ↑(ρD.ψ v i g') =
        algebraMap C (lauSub (ρ.part C)) (χ v i g - χ v i g') := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, hψ, hψ]
      show _ = AddMonoidAlgebra.single 0 (algebraMap C K (χ v i g - χ v i g'))
      rw [map_sub, hχe, hχe, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgGlue
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_glue :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing D] [Algebra O D] (𝔪 : Ideal D), ⨅ N : ℕ, 𝔪 ^ N = ⊥ → ∀ f : ∀ N : ℕ, A →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ a, ∃ d, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N a) → ∃ ξ : A →ₐ[O] D, ∀ a N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N a := by
  intro O A D _ _ _ _ _ 𝔪 hm f hf
  choose g hg using hf
  have uniq : ∀ x y : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) x
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) y) → x = y := by
    intro x y h
    have hxy : x - y ∈ (⨅ N : ℕ, 𝔪 ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.Quotient.eq.1 (h N))
    rw [hm, Ideal.mem_bot] at hxy
    exact sub_eq_zero.1 hxy
  refine ⟨{ toFun := g
            map_one' := uniq _ _ fun N => by rw [hg, map_one, map_one]
            map_mul' := fun a b => uniq _ _ fun N => by rw [hg, map_mul, map_mul, hg, hg]
            map_zero' := uniq _ _ fun N => by rw [hg, map_zero, map_zero]
            map_add' := fun a b => uniq _ _ fun N => by rw [hg, map_add (f := _), map_add (f := _), hg, hg]
            commutes' := fun r => uniq _ _ fun N => by
              rw [hg, AlgHom.commutes]; rfl }, fun a N => hg a N⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgHomog
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.single_coeff_mul {K : Type} [CommRing K] (p q : AddMonoidAlgebra K ℤ) (j : ℤ) :
    AddMonoidAlgebra.single j ((p * q).coeff j) = ∑ a ∈ p.coeff.support,
      AddMonoidAlgebra.single a (p.coeff a) * AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) := by
  classical
  have key : ∀ a : ℤ, AddMonoidAlgebra.single a (p.coeff a) *
      AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) =
        AddMonoidAlgebra.single j (p.coeff a * q.coeff (-a + j)) := by
    intro a
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
  simp_rw [key]
  have hc : (p * q).coeff j = ∑ a ∈ p.coeff.support, p.coeff a * q.coeff (-a + j) := by
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.sum]
    have hcond : ∀ b : ℤ, (a + b = j) ↔ (b = -a + j) := fun b => by omega
    simp_rw [hcond]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hm, mul_zero]
  rw [hc]
  ext k
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  split_ifs with hk
  · rfl
  · simp

theorem UpperTheory.V.Fr.alg_homog :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
      {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (p : lauSub P),
      p ∈ vertex h ^ N → ∀ j : ℤ,
        (⟨AddMonoidAlgebra.single j (p.1.coeff j), single_mem_lauSub P (p.2 j)⟩ : lauSub P) ∈
          vertex h ^ N := by
  intro C K _ _ _ _ P _ h N
  let comp : lauSub P → ℤ → lauSub P := fun q k =>
    ⟨AddMonoidAlgebra.single k (q.1.coeff k), single_mem_lauSub P (q.2 k)⟩
  have hcomp : ∀ q k, (comp q k).1 = AddMonoidAlgebra.single k (q.1.coeff k) := fun _ _ => rfl
  have base : ∀ q : lauSub P, q ∈ vertex h → ∀ k : ℤ, comp q k ∈ vertex h := by
    intro q hq k
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = q.1.coeff 0 at hq
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp q k).1.coeff 0
    obtain ⟨c, hc, hce⟩ := hq
    rw [hcomp, AddMonoidAlgebra.coeff_single]
    by_cases hk : k = 0
    · subst hk
      exact ⟨c, hc, by rw [Finsupp.single_eq_same, hce]⟩
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hk, map_zero]⟩
  show ∀ p : lauSub P, p ∈ vertex h ^ N → ∀ j, comp p j ∈ vertex h ^ N
  induction N with
  | zero =>
    intro p _ j
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun r => ∀ j, comp r j ∈ vertex h ^ (n + 1)) hp ?_ ?_
    · intro x hx y hy j
      have e : comp (x * y) j =
          ∑ a ∈ x.1.coeff.support, comp x a * comp y (-a + j) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, hcomp, Subalgebra.coe_mul, single_coeff_mul]
        rfl
      rw [e, pow_succ]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih x hx a) (base y hy _)
    · intro x y hx hy j
      have e : comp (x + y) j = comp x j + comp y j := by
        apply Subtype.ext
        simp only [hcomp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          AddMonoidAlgebra.single_add]
      rw [e]
      exact add_mem (hx j) (hy j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLift
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem adicCont_ringHom_comp_of_map_mem {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f : R →+* S) (hIJ : ∀ x ∈ I, f x ∈ J) {u : Γ → R}
    (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hle : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) N
  have hc := (hu N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert hc using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Fr.alg_lift :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsModel O C 𝔪 ρ → ∀ (Q : Type) [CommRing Q] [Algebra O Q] [IsCO O Q] (p : D →ₐ[O] Q), (∀ x ∈ 𝔪, p x ∈ maximalIdeal Q) → IsLift O (ρ.map (p : D →+* Q)) := by
  intro l _ O _ _ F n C _ _ _ D _ _ _ _ 𝔪 ρ hm Q _ _ _ p hp
  have hres : ∀ c : C, res O Q (p (algebraMap C D c)) = res O C c := fun c =>
    res_map (p.comp (IsScalarTower.toAlgHom O C D)) c
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.1 i j)
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.2 v i)
  · obtain ⟨c, hc1, hc2⟩ := hm.dg g i
    show res O Q (p (ρ.r g i i)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · obtain ⟨c, hc1, hc2⟩ := hm.psi v i g
    show res O Q (p ↑(ρ.ψ v i g)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · show res O Q (p (ρ.r g i j)) = 0
    rw [res_eq_zero_iff]
    exact hp _ (hm.off g i j hij)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgQuot
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem adicComplete_of_pow_eq_bot {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (h : I ^ n = ⊥) :
    IsAdicComplete I R := by
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [h, Submodule.bot_smul] at hxy
    exact SModEq.bot.mp hxy
  refine { haus' := fun x hx => key x 0 (hx n), prec' := fun {f} hf => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hnm
  · exact hf hmn
  · rw [key _ _ (hf hnm)]

theorem UpperTheory.V.Fr.alg_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ N : ℕ, ∃ h : IsCO O (D ⧸ 𝔪 ^ (N + 1)), @maximalIdeal _ _ h.toIsLocalRing = 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
  intro O _ _ C _ _ _ D _ _ _ _ 𝔪 hV N
  have hle : 𝔪 ^ (N + 1) ≤ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hmax : 𝔪.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      have h1' : (1 : C) ∈ 𝔪.comap (algebraMap C D) := by
        rw [Ideal.mem_comap, map_one]
        exact h1
      rw [hV.comap] at h1'
      exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).mpr h1')
    · intro J x hJ hx hxJ
      obtain ⟨c, hc⟩ := hV.surj x
      have hcu : IsUnit c := by
        by_contra hnu
        have hcm : c ∈ maximalIdeal C := hnu
        rw [← hV.comap, Ideal.mem_comap] at hcm
        apply hx
        have := 𝔪.add_mem hc hcm
        rwa [sub_add_cancel] at this
      have hcJ : algebraMap C D c ∈ J := by
        have := J.sub_mem hxJ (hJ hc)
        rwa [sub_sub_cancel] at this
      rw [Ideal.eq_top_of_isUnit_mem J hcJ (hcu.map _)]
      exact Submodule.mem_top
  set M : Ideal (D ⧸ 𝔪 ^ (N + 1)) := 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) with hM
  have hmem : ∀ d : D, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d ∈ M ↔ d ∈ 𝔪 :=
    fun d => Ideal.mem_quotient_iff_mem hle
  have hMmax : M.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (𝔪 ^ (N + 1)))
      Ideal.Quotient.mk_surjective hmax with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) 1 ∈ M := by
        rw [← hM] at h
        rw [h]
        exact Submodule.mem_top
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mp h1))
    · exact h
  have hMpow : M ^ (N + 1) = ⊥ := by
    rw [hM, ← Ideal.map_pow, Ideal.map_quotient_self]
  have hnil : nilradical (D ⧸ 𝔪 ^ (N + 1)) = M := by
    apply le_antisymm
    · exact nilradical_le_prime M
    · intro x hx
      refine ⟨N + 1, ?_⟩
      have := Ideal.pow_mem_pow hx (N + 1)
      rw [hMpow] at this
      exact (Submodule.mem_bot _).mp this
  haveI : (nilradical (D ⧸ 𝔪 ^ (N + 1))).IsMaximal := hnil ▸ hMmax
  haveI hloc : IsLocalRing (D ⧸ 𝔪 ^ (N + 1)) := IsLocalRing.of_isMaximal_nilradical _
  have hMeq : maximalIdeal (D ⧸ 𝔪 ^ (N + 1)) = M := (IsLocalRing.eq_maximalIdeal hMmax).symm
  have halg : ∀ a : O, algebraMap O (D ⧸ 𝔪 ^ (N + 1)) a
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (algebraMap O C a)) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  haveI : IsNoetherianRing D := hV.noeth
  refine ⟨@IsCO.mk O (D ⧸ 𝔪 ^ (N + 1)) _ _ _ _ hloc inferInstance ?_ ?_ ?_, hMeq⟩
  · rw [hMeq]
    exact adicComplete_of_pow_eq_bot M (N + 1) hMpow
  · refine ⟨fun a ha => ?_⟩
    have hC : IsUnit (algebraMap O C a) := by
      by_contra hnu
      have hcm : algebraMap O C a ∈ maximalIdeal C := hnu
      rw [← hV.comap, Ideal.mem_comap, ← hmem, ← halg, ← hMeq] at hcm
      exact hcm ha
    exact (IsCO.isLocalHom (O := O) (R := C)).map_nonunit a hC
  · intro x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := hV.surj d
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) c
    refine ⟨a, ?_⟩
    rw [hMeq, halg, ← map_sub, hmem]
    have hca : algebraMap C D (c - algebraMap O C a) ∈ 𝔪 := by
      rw [← Ideal.mem_comap, hV.comap]
      exact ha
    have := 𝔪.add_mem hc hca
    rwa [map_sub, sub_add_sub_cancel] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_rev (n : ℕ) (i : Fin n) : w n i.rev = - w n i := by
  have := i.isLt
  simp only [w, Fin.val_rev]
  split_ifs <;> omega

private theorem J_apply {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ k : Fin n, (j = k.rev) ↔ (k = j.rev) := by
    intro k
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def tw {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun X := Matrix.of fun i j => ((u ^ (w n i - w n j) : Kˣ) : K) * X i j
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : w n i - w n j = (w n i - w n a) + (w n a - w n j) := by ring
    rw [this, _root_.zpow_add, Units.val_mul]
    ring
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp [mul_add]
  commutes' c := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem tw_apply {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    tw n u X i j = ((u ^ (w n i - w n j) : Kˣ) : K) * X i j := rfl

private theorem ordProd_tw {H K : Type} [CommRing K] {n : ℕ} (u : Kˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => tw n u (r s)) ψ g = tw n u (ordProd r ψ g) := by
  unfold ordProd
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

theorem UpperTheory.V.Fr.alg_twist :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K] (u : Kˣ) (ρ : NRep F n K), ∃ ρ' : NRep F n K, (∀ g i j, ρ'.r g i j = ((u ^ (w n i - w n j) : Kˣ) : K) * ρ.r g i j) ∧ ρ'.ψ = ρ.ψ := by
  intro l _ k _ F n K _ u ρ
  refine ⟨⟨(tw n u).toRingHom.toMonoidHom.comp ρ.r, ρ.ψ, ?_, ?_, ?_⟩, fun g i j => rfl, rfl⟩
  · intro g
    ext i j
    rw [J_apply]
    show tw n u (ρ.r (F.star g)) i j = tw n u (ρ.r g) j.rev i.rev
    rw [tw_apply, tw_apply, ρ.pol, J_apply, w_rev, w_rev]
    congr 3
    ring
  · intro i j h
    have := ρ.diag i j h
    rw [Matrix.sub_apply] at this ⊢
    show tw n u (ρ.r F.g0) i j - tw n u (ρ.r (F.star F.g0)) i j = 0
    rw [tw_apply, tw_apply, ← mul_sub, this, mul_zero]
  · intro v g
    have := ordProd_tw u (fun s => ρ.r (F.loc0 v s)) (fun i s => ((ρ.ψ v i s : Kˣ) : K)) g
    exact this.trans (by rw [ρ.ord, map_zero])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerOrderSkips
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ch2 {K : Type} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    M * (M.trace • (1 : Matrix (Fin 2) (Fin 2) K) - M) = M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem UpperTheory.V.Fr.frobenius_corner_order_skips :
    ∀ {H K : Type} [Group H] [CommRing K] (σ : H →* Matrix (Fin 2) (Fin 2) K) (a : H → K) (c : H →* K) (g₁ : H) (t : K), IsUnit (σ g₁ - t • (1 : Matrix (Fin 2) (Fin 2) K)).det → (∀ x y, (σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ g₁ - t • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) → ∀ x y, (σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := by
  intro H K _ _ σ a c g t hu h x y
  set P := σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K) with hP
  set M := σ g - t • (1 : Matrix (Fin 2) (Fin 2) K) with hM
  have hQ : ∀ z, P * M * σ z = c z • (P * M) := fun z => by
    have := h x z
    rw [mul_sub, Matrix.mul_smul, mul_one, sub_eq_zero] at this
    exact this
  have h0 : P * M * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := h x y
  have h1 : P * M * M = (c g - t) • (P * M) := by
    conv_lhs => rw [show P * M * M = P * M * (σ g - t • (1 : Matrix (Fin 2) (Fin 2) K)) from rfl]
    rw [mul_sub, hQ, Matrix.mul_smul, mul_one, sub_smul]
  have h2 : M.det • P = (M.trace - (c g - t)) • (P * M) := by
    calc M.det • P = P * (M * (M.trace • (1 : Matrix (Fin 2) (Fin 2) K) - M)) := by
          rw [ch2, Matrix.mul_smul, mul_one]
      _ = _ := by rw [← mul_assoc, mul_sub, h1, Matrix.mul_smul, mul_one, ← sub_smul]
  have h3 : M.det • (P * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K))) = 0 := by
    rw [← Matrix.smul_mul, h2, Matrix.smul_mul, h0, smul_zero]
  exact (hu.smul_eq_zero).1 h3
end

