module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinors
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem kMinor_comp_perm {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ)
    (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    kMinor A k hk (I ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : F) * kMinor A k hk I := by
  unfold kMinor
  have e : A.submatrix (I ∘ σ) (Fin.castLE hk) = (A.submatrix I (Fin.castLE hk)).submatrix σ id := by
    ext a b
    simp
  rw [e, Matrix.det_permute]

theorem normAt_comp_perm {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) (h : NormAt O Y k hk I) :
    NormAt O Y k hk (I ∘ σ) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, fun J => ?_⟩
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h0
    · simpa [hs] using h0
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h1 J
    · simpa [hs, div_neg] using O.neg_mem (h1 J)

theorem exists_perm_castSucc {k : ℕ} (f : Fin k → Fin (k + 1)) (hf : Function.Injective f) :
    ∃ g : Equiv.Perm (Fin (k + 1)), ∀ a : Fin k, g a.castSucc = f a := by
  classical
  let e : {x // x ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1))} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  have h := e.extendSubtype_apply_of_mem a.castSucc ⟨a, rfl⟩
  rw [h]
  have h2 : (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm
      ⟨a.castSucc, ⟨a, rfl⟩⟩ = a := Equiv.ofInjective_symm_apply _ a
  simp only [e, Equiv.trans_apply]
  erw [h2]
  rfl

def castEmb {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩

theorem exists_perm_restrict {m j r : ℕ} (hm : m ≤ j) (hj : j ≤ r) (hmr : m ≤ r)
    (g : Equiv.Perm (Fin m)) :
    ∃ σ : Equiv.Perm (Fin j), ∀ a : Fin j,
      g.viaFintypeEmbedding (castEmb hmr) (Fin.castLE hj a) = Fin.castLE hj (σ a) := by
  classical
  refine ⟨g.viaFintypeEmbedding (castEmb hm), fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have e1 : Fin.castLE hj a = castEmb hmr ⟨a, ha⟩ := by ext; simp [castEmb]
    have e2 : a = castEmb hm ⟨a, ha⟩ := by ext; simp [castEmb]
    rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image]
    conv_rhs => rw [e2, Equiv.Perm.viaFintypeEmbedding_apply_image]
    ext; simp [castEmb]
  · have n1 : Fin.castLE hj a ∉ Set.range (castEmb hmr) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    have n2 : a ∉ Set.range (castEmb hm) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n1,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n2]

theorem exists_perm_top {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (I : Fin r → Fin r) (h : NormAt O Y r le_rfl I) : ∃ w : Equiv.Perm (Fin r), ⇑w = I := by
  have hinj : Function.Injective I := by
    intro a b hab
    by_contra hne
    refine h.1 ?_
    unfold kMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    ext c
    simp [hab]
  exact ⟨Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj), rfl⟩

theorem perm_step {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F) (k : ℕ)
    (hk : k + 1 ≤ r) (w : Equiv.Perm (Fin r)) (f : Fin k → Fin (k + 1)) (hf : Function.Injective f)
    (hw : ∀ (j : ℕ) (hj : j ≤ r), k + 1 ≤ j → NormAt O Y j hj (w ∘ Fin.castLE hj))
    (hn : NormAt O Y k (Nat.le_of_succ_le hk) ((w ∘ Fin.castLE hk) ∘ f)) :
    ∃ w' : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), k ≤ j → NormAt O Y j hj (w' ∘ Fin.castLE hj) := by
  classical
  obtain ⟨g, hg⟩ := exists_perm_castSucc f hf
  refine ⟨w * g.viaFintypeEmbedding (castEmb hk), fun j hj hkj => ?_⟩
  rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
  · have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hk) ∘ f := by
      funext a
      have e1 : Fin.castLE hj a = castEmb hk a.castSucc := by ext; simp [castEmb]
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image, hg]
      rfl
    rw [e]
    exact hn
  · obtain ⟨σ, hσ⟩ := exists_perm_restrict (m := k + 1) (j := j) hlt hj hk g
    have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hj) ∘ σ := by
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [hσ]
    rw [e]
    exact normAt_comp_perm O Y j hj _ σ (hw j hj hlt)

theorem exists_perm_normAt {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (hex : ∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r),
      NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I →
        ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧
          NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f))
    (hall : ∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  have key : ∀ d : ℕ, d ≤ r → ∃ w : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), r - d ≤ j →
      NormAt O Y j hj (w ∘ Fin.castLE hj) := by
    intro d
    induction d with
    | zero =>
      intro _
      obtain ⟨I, hI⟩ := hall r le_rfl
      obtain ⟨w, hw⟩ := exists_perm_top O Y I hI
      refine ⟨w, fun j hj hrj => ?_⟩
      have hjr : j = r := le_antisymm hj (by simpa using hrj)
      subst hjr
      have e : (⇑w ∘ Fin.castLE hj) = I := by
        funext a
        simp [hw]
      rw [e]
      exact hI
    | succ d ih =>
      intro hd
      obtain ⟨w, hw⟩ := ih (by omega)
      obtain ⟨k, hkd⟩ : ∃ k, k + 1 = r - d := ⟨r - d - 1, by omega⟩
      have hk : k + 1 ≤ r := by omega
      obtain ⟨I, hI⟩ := hall k (Nat.le_of_succ_le hk)
      obtain ⟨f, hf, hn⟩ := hex k hk (w ∘ Fin.castLE hk) I (hw _ hk (by omega)) hI
      obtain ⟨w', hw'⟩ := perm_step O Y k hk w f hf (fun j hj h => hw j hj (by omega)) hn
      exact ⟨w', fun j hj h => hw' j hj (by omega)⟩
  obtain ⟨w, hw⟩ := key r le_rfl
  exact ⟨w, fun k hk => hw k hk (by omega)⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  have hbase : f.base = g.base := by
    ext q
    exact hb q
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun q hq => ?_
  have hqg : g q ∈ U := hq
  have hqf : f q ∈ U := by rw [hb q]; exact hqg
  have hpf : genPt ξ ⤳ f q := RegAtDom.map_genPt hf ▸ (hall q).map f.continuous
  have hpg : genPt ξ ⤳ g q := RegAtDom.map_genPt hg ▸ (hall q).map g.continuous
  have key : ∀ (a b : X) (_ : a = b) (ha : genPt ξ ⤳ a) (hb : genPt ξ ⤳ b) (h1 : a ∈ U) (h2 : b ∈ U),
      genMap ξ ⟨a, ha⟩ ((X.presheaf.germ U a h1).hom s) = genMap ξ ⟨b, hb⟩ ((X.presheaf.germ U b h2).hom s) := by
    rintro a _ rfl ha hb h1 h2
    rfl
  apply hgen.inj ⟨q, hall q⟩
  have e1 := RegAtDom.genMap_stalkMap hf q (hall q) hpf ((X.presheaf.germ U (f q) hqf).hom s)
  have e2 := RegAtDom.genMap_stalkMap hg q (hall q) hpg ((X.presheaf.germ U (g q) hqg).hom s)
  rw [Scheme.Hom.germ_stalkMap_apply] at e1 e2
  have e3 := key _ _ (hb q) hpf hpg hqf hqg
  rw [← e3, ← e1] at e2
  refine (congrArg (genMap ξ' ⟨q, hall q⟩) ?_).trans e2.symm
  exact TopCat.Presheaf.germ_res_apply X'.presheaf _ q hqg _

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chRing_basicOpen_basis o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end GlobalTheory.CompanionTheory.Ar.ChMorph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualActionCompat
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

theorem exists_retraction_mod : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (m : ℕ), Module.Projective A (D.omHT σ) → (∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y') → ∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ m hproj hsurj
  classical
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : ((p : K) ^ m) ≠ 0 := pow_ne_zero _ hp
  have hmemM : ∀ w ∈ D.om', eigProj D.ρΩ σ w ∈ D.omHT σ := fun w hw => ⟨w, hw, rfl⟩
  have hh : ∀ i : Fin N, D.h (Pi.single i 1) ∈ D.om' := fun i =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)
  let v : Fin N → D.omHT σ := fun i => ⟨eigProj D.ρΩ σ (D.h (Pi.single i 1)), hmemM _ (hh i)⟩
  let Q : (Fin N → A) →ₗ[A] D.omHT σ := Fintype.linearCombination A v
  have hQ : ∀ x, ((Q x : D.omHT σ) : Module.Dual K Li) = D.q σ x := by
    intro x
    simp [Q, Fintype.linearCombination_apply, HTChart.q, v]
  let P : Submodule A (D.omHT σ) := LinearMap.range (((p : A) ^ m) • (LinearMap.id : D.omHT σ →ₗ[A] D.omHT σ))
  have hsurjQ : Function.Surjective (P.mkQ ∘ₗ Q) := by
    intro y
    obtain ⟨z, rfl⟩ := P.mkQ_surjective y
    obtain ⟨x, y', hy', h⟩ := hsurj z z.2
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨-⟨y', hy'⟩, ?_⟩
    apply Subtype.ext
    simp [hQ, h]
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ Q) P.mkQ hsurjQ
  have hr' : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, Q (r z) = z + ((p : A) ^ m) • z' := by
    intro z
    have := LinearMap.congr_fun hr z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.eq] at this
    obtain ⟨z', hz'⟩ := this
    refine ⟨z', ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz'
    rw [hz']; abel
  have hvec := fun k => HTL.exists_vec D ρ hc hact σ ((LinearMap.proj k) ∘ₗ r)
  choose ev hev hevz using hvec
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K ev
  have hRr : ∀ x, Rr x = ∑ k, x k • ev k := fun x => by simp [Rr, Fintype.linearCombination_apply]
  have hzL : ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range,
      ∀ z : D.omHT σ, (z : Module.Dual K Li) e ∈ (algebraMap A K).range := by
    intro e he z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = z := hz
    rw [← hz', eigProj_apply D ρ hc hact σ he.1 w]
    simpa using he.2 w hw
  refine ⟨Rr, fun k => ?_, fun e he => ?_⟩
  · have h1 : Rr (Pi.single k 1) = ev k := by simp [hRr, Pi.single_apply]
    rw [h1]
    refine ⟨hev k, fun w hw => ?_⟩
    rw [one_mul, ← eigProj_apply D ρ hc hact σ (hev k) w]
    exact ⟨_, (hevz k ⟨_, hmemM w hw⟩).symm⟩
  · let x : Fin N → K := fun l => D.h (Pi.single l 1) e
    have hRx : Rr x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      rw [hRr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hev k)
    have key : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, (z : Module.Dual K Li) (Rr x) =
        (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
      intro z
      obtain ⟨z', hz'⟩ := hr' z
      refine ⟨z', ?_⟩
      have h1 : (z : Module.Dual K Li) (Rr x) = ∑ k, x k * algebraMap A K (r z k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hRr, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hevz k z]
        rfl
      have h2 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e = ∑ k, algebraMap A K (r z k) * x k := by
        rw [hQ, HTChart.q, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [LinearMap.smul_apply, eigProj_apply D ρ hc hact σ he.1, Algebra.smul_def]
      have h3 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e =
          (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
        rw [hz']
        simp [Algebra.smul_def]
      rw [h1, ← h3, h2]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsub := Submodule.sub_mem _ hRx he.1
    refine ⟨((p : K) ^ m)⁻¹ • (Rr x - e), ⟨Submodule.smul_mem _ _ hsub, fun w hw => ?_⟩, ?_⟩
    · rw [one_mul, ← eigProj_apply D ρ hc hact σ (Submodule.smul_mem _ _ hsub) w]
      obtain ⟨z', hz'⟩ := key ⟨_, hmemM w hw⟩
      have hval : eigProj D.ρΩ σ w (((p : K) ^ m)⁻¹ • (Rr x - e)) = (z' : Module.Dual K Li) e := by
        rw [map_smul, map_sub]
        have : eigProj D.ρΩ σ w (Rr x) = eigProj D.ρΩ σ w e + (p : K) ^ m * (z' : Module.Dual K Li) e := hz'
        rw [this, add_sub_cancel_left, smul_eq_mul, inv_mul_cancel_left₀ hpm]
      rw [hval]
      exact hzL e he z'
    · rw [smul_smul, mul_inv_cancel₀ hpm, one_smul]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGeneratorInvertConstant
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lattice_generator_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_spread

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticePatchAtPrimes
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.patch_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (q : Cpt ξ), (∀ p ∈ S, p.Prime) →
    ((∀ p ∈ S, ¬ InFibre ξ p q) → Lat.patch S L₀ Lp q = L₀ q) ∧
      ∀ p ∈ S, InFibre ξ p q → Lat.patch S L₀ Lp q = Lp p q := by
  intro X Ω _ ξ E _ _ S L₀ Lp q hS
  exact ⟨fun h => Lat.patch_of_not S L₀ Lp h, fun p hp h => Lat.patch_of_unique S L₀ Lp hp h
    fun p' hp' h' => inFibre_unique (hS p hp) (hS p' hp') h h'⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormScaleConjugateInvariant
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem kappa_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (M : ℕ) (f g : MRing ι) (dg : K → ℕ)
    (κ : (F →+* ℂ) → ℝ), OverInt y φ → 0 < M → IsMultiHomog g dg → g ∉ mCoordIdeal y → IsConjInvariantH A →
    (∀ σ, 0 < κ σ) → (∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖) →
    ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ := by
  intro K _ ι _ Ω _ F _ _ y φ A M f g dg κ hO hM hg hgy hA hκ hN σ
  obtain ⟨z, hz, hgz⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_ptOver_ne K ι Ω F y φ σ g dg hO hg hgy
  have h1 := hN σ z hz
  have h2 := hN _ _ (ptOver_conj K ι Ω F y φ σ z hz)
  rw [evC_conj, evC_conj, hA z, RCLike.norm_conj, RCLike.norm_conj] at h2
  have hgn : ‖evC z g‖ ≠ 0 := norm_ne_zero_iff.2 hgz
  have hh : 0 < A.h z := A.pos z hz.1.1
  have h3 : (κ (ComplexEmbedding.conjugate σ) * A.h z) ^ M = (κ σ * A.h z) ^ M :=
    mul_right_cancel₀ hgn (h2.symm.trans h1)
  have h4 := (pow_left_inj₀ (mul_pos (hκ _) hh).le (mul_pos (hκ _) hh).le hM.ne').1 h3
  exact mul_right_cancel₀ hh.ne' h4

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

