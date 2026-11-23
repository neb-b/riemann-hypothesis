module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.G3 (bcMap bcMap_fst bcMap_snd)
open UpperTheory.Gal.Int.Geo (KS Lv)

private theorem level_isPullback {S S' B B' Z : Scheme.{0}} {A : Over S} {A' : Over S'} {s : S ⟶ B'} {s' : S' ⟶ B}
    {f : S' ⟶ S} {g : B ⟶ B'} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ f)
    (H : IsPullback φ A'.hom A.hom f) (hf : IsPullback f s' s g) (k : ℕ) {q : Z ⟶ B'}
    (e : Z ≅ (GlobalTheory.KS.pow A k).left) (he : e.hom ≫ (GlobalTheory.KS.pow A k).hom ≫ s = q) :
    IsPullback (GlobalTheory.KS.powMap f φ hφ k ≫ e.inv) ((GlobalTheory.KS.pow A' k).hom ≫ s') q g := by
  have P := (GlobalTheory.KS.PowPB.powMap_isPullback S S' A A' f φ hφ H k).paste_vert hf
  have Q : IsPullback e.inv ((GlobalTheory.KS.pow A k).hom ≫ s) q (𝟙 B') := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← he, Category.comp_id, Iso.inv_hom_id_assoc]
  have R := P.paste_horiz Q
  rw [Category.comp_id] at R
  exact R

private theorem pow_square (pc : PowComp) {S₁ S₂ S₁' S₂' : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {f₁ : S₁' ⟶ S₁} {f₂ : S₂' ⟶ S₂} {π : S₂ ⟶ S₁} {π' : S₂' ⟶ S₁'} {φ₁ : A₁'.left ⟶ A₁.left}
    {φ₂ : A₂'.left ⟶ A₂.left} {χ : A₂.left ⟶ A₁.left} {χ' : A₂'.left ⟶ A₁'.left}
    (h₁ : φ₁ ≫ A₁.hom = A₁'.hom ≫ f₁) (h₂ : φ₂ ≫ A₂.hom = A₂'.hom ≫ f₂)
    (hχ : χ ≫ A₁.hom = A₂.hom ≫ π) (hχ' : χ' ≫ A₁'.hom = A₂'.hom ≫ π')
    (hπ : π' ≫ f₁ = f₂ ≫ π) (hc : χ' ≫ φ₁ = φ₂ ≫ χ) (k : ℕ) :
    GlobalTheory.KS.powMap π' χ' hχ' k ≫ GlobalTheory.KS.powMap f₁ φ₁ h₁ k = GlobalTheory.KS.powMap f₂ φ₂ h₂ k ≫ GlobalTheory.KS.powMap π χ hχ k := by
  have h₃ : (φ₂ ≫ χ) ≫ A₁.hom = A₂'.hom ≫ (f₂ ≫ π) := by
    rw [Category.assoc, hχ, ← Category.assoc, h₂, Category.assoc]
  rw [pc _ _ _ A₂' A₁' A₁ π' f₁ (f₂ ≫ π) χ' φ₁ (φ₂ ≫ χ) hχ' h₁ h₃ hπ hc k,
    pc _ _ _ A₂' A₂ A₁ f₂ π (f₂ ≫ π) φ₂ χ (φ₂ ≫ χ) h₂ hχ h₃ rfl rfl k]

private theorem level_tr {S₁ S₂ S₁' S₂' B B' Z₁ Z₂ : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {q₁ : Z₁ ⟶ B'} {q₂ : Z₂ ⟶ B'} {g : B ⟶ B'} {k : ℕ} {s₁' : S₁' ⟶ B} {s₂' : S₂' ⟶ B}
    {Φ₁ : (GlobalTheory.KS.pow A₁' k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Φ₂ : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₂ k).left}
    {Ψ : (GlobalTheory.KS.pow A₂ k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Ψ' : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₁' k).left}
    {π' : S₂' ⟶ S₁'} (hΨ' : Ψ' ≫ (GlobalTheory.KS.pow A₁' k).hom = (GlobalTheory.KS.pow A₂' k).hom ≫ π') (hs : π' ≫ s₁' = s₂')
    (hsq : Ψ' ≫ Φ₁ = Φ₂ ≫ Ψ) (e₁ : Z₁ ≅ (GlobalTheory.KS.pow A₁ k).left) (e₂ : Z₂ ≅ (GlobalTheory.KS.pow A₂ k).left)
    (t : Z₂ ⟶ Z₁) (ht : t ≫ q₁ = q₂) (he : t ≫ e₁.hom = e₂.hom ≫ Ψ)
    (P₁ : IsPullback (Φ₁ ≫ e₁.inv) ((GlobalTheory.KS.pow A₁' k).hom ≫ s₁') q₁ g)
    (P₂ : IsPullback (Φ₂ ≫ e₂.inv) ((GlobalTheory.KS.pow A₂' k).hom ≫ s₂') q₂ g) :
    bcMap g t ht ≫ P₁.isoPullback.symm.hom = P₂.isoPullback.symm.hom ≫ Ψ' := by
  have hΨ : Ψ ≫ e₁.inv = e₂.inv ≫ t := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply P₁.hom_ext
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst, bcMap_fst]
    rw [reassoc_of% hsq, hΨ, ← Category.assoc Φ₂ e₂.inv t, IsPullback.isoPullback_inv_fst_assoc]
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd, bcMap_snd]
    rw [reassoc_of% hΨ', hs, IsPullback.isoPullback_inv_snd]

theorem UpperTheory.Gal.LocalSmoothExtension.kSBc_of :
    ModelBc → LegBc → PowComp → KSBc := by
  intro hmod hleg pc p _ D G L R _ _ gb k T τ gb' hρ ht
  have ht' : ∀ i, gb'.t i = τ.comp (gb.t i) := fun i => RingHom.ext fun c => ht i c
  have hM := fun N : Lv p => hmod D.toG R ℂ τ gb gb' hρ ht' (↑N) (T.M N)
  choose M' f hpb hm using hM
  let m := fun N => (hm N).some
  have hφ : ∀ N, (m N).φ ≫ (T.M N).univ.A.hom = (M' N).univ.A.hom ≫ f N := fun N => (m N).cart.1.w
  have P : ∀ N, IsPullback (GlobalTheory.KS.powMap (f N) (m N).φ (hφ N) k ≫ (T.e N).inv)
      ((GlobalTheory.KS.pow (M' N).univ.A k).hom ≫ (M' N).s) (T.X.q (T.lev N)) (Spec.map (CommRingCat.ofHom τ)) :=
    fun N => level_isPullback (hφ N) (m N).cart.1 (hpb N) k (T.e N) (T.e_q N)
  refine ⟨UpperTheory.Gal.Int.Geo.KS.mk (towerBc T.X (Spec.map (CommRingCat.ofHom τ))) T.lev T.K_eq T.Δ_eq M'
    (fun N => (P N).isoPullback.symm) ?_ ?_, rfl, HEq.rfl⟩
  · intro N
    exact (P N).isoPullback_inv_snd
  · intro N' N h a b
    obtain ⟨π₀, o₀, ψ₀, φ₀, hw₀, hs₀, htr₀, he₀⟩ := T.tr_eq N' N h a b
    obtain ⟨π₁, o₁, ψ₁, φ₁, hs₁, htr₁, hπ, hc⟩ := hleg p D G L R ℂ τ gb gb' hρ ht' N N' (T.M N) (T.M N')
      (M' N) (M' N') (f N) (f N') (hpb N) (hpb N') (m N) (m N') h π₀ o₀ ψ₀ φ₀ hs₀ htr₀
    have hw₁ : (Over.Hom.left ψ₁ ≫ φ₁.φ) ≫ (M' N).univ.A.hom = (M' N').univ.A.hom ≫ π₁ := by
      rw [Category.assoc, φ₁.cart.1.w, ← Category.assoc, Over.w]
    refine ⟨π₁, o₁, ψ₁, φ₁, hw₁, hs₁, htr₁, ?_⟩
    exact level_tr (GlobalTheory.KS.PowPB.powMap_w π₁ _ hw₁ k) hs₁
      (pow_square pc (hφ N) (hφ N') hw₀ hw₁ hπ hc k) (T.e N) (T.e N') _ (T.X.tr_q _ _ h a b) he₀ (P N) (P N')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntFn
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntFn_of :
    CntFn := by
  intro Γ _ K K' M h hKK' hMn hidx hconj
  have hrep : ∀ (c m : K'), m ∈ M.subgroupOf K' → ∀ y : Γ,
      (h * ((c * m : K') : Γ) * y ∈ K ↔ h * (c : Γ) * y ∈ K) := by
    intro c m hm y
    have hm' : (m : Γ) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have key : h * ((c * m : K') : Γ) * y = (h * (c : Γ) * m * (h * c)⁻¹) * (h * c * y) := by
      push_cast
      group
    rw [key]
    exact Subgroup.mul_mem_cancel_left K (hconj c c.2 m hm')
  have hnz : ∀ y : Γ, cntFn K K' M h y ≠ 0 →
      ∃ q : K' ⧸ M.subgroupOf K', h * ((Quotient.out q : K') : Γ) * y ∈ K := by
    intro y hy
    unfold cntFn at hy
    obtain ⟨⟨q, hq⟩⟩ := (Nat.card_ne_zero.mp (Nat.cast_ne_zero.mp hy)).1
    exact ⟨q, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk y
    constructor
    · haveI : (M.subgroupOf K').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hMn g g.2 n hn⟩
      unfold cntFn
      congr 1
      refine Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.mulRight (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K'))) ?_)
      intro q
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out q * ⟨k, hKK' hk⟩)
      have hq : q * (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')) =
          ((Quotient.out q * ⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K') := by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
      simp only [Equiv.coe_mulRight]
      rw [hq, hm, hrep _ _ m.2]
      simp only [Subgroup.coe_mul, mul_assoc]
    · unfold cntFn
      simp only [← mul_assoc, Subgroup.mul_mem_cancel_right K hk]
  · intro y hy
    obtain ⟨q, hq⟩ := hnz y hy
    refine ⟨(h * ((Quotient.out q : K') : Γ) * y)⁻¹, K.inv_mem hq, _, (Quotient.out q).2, ?_⟩
    group
  · haveI : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
    refine (Set.finite_range (fun q : K' ⧸ M.subgroupOf K' =>
      ((((Quotient.out q : K') : Γ)⁻¹ * h⁻¹ : Γ) : Γ ⧸ K))).subset ?_
    intro y hy
    obtain ⟨q, hq⟩ := hnz _ hy
    refine ⟨q, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hq
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntSum_of :
    CntSum := by
  classical
  intro Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP
  have hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c) := by
    intro c hc u hu
    have e := hP _ (hconj c hc u hu) c hc
    rw [← e]
    congr 1
    group
  let φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K' := fun z =>
    QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, x⟩ ⟨a', x'⟩ he
      simp only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he
      push_cast at he
      have hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K := by
        have e := K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))
        convert e using 1
        group
      have ha : a = a' := by
        rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        push_cast
        exact hK
      subst ha
      have hx1 : r x' * (r x')⁻¹ ∈ M := by simpa using M.one_mem
      have hx2 : r x' * (r x)⁻¹ ∈ M := by
        have e := hnorm (r x) (hKK' (hrK x)) _ he
        convert e using 1
        group
      obtain ⟨x0, _, hu⟩ := hr (r x') (hrK x')
      rw [hu x hx2, hu x' hx1]
    · intro b
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c
      have hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K := by
        rw [hk]
        push_cast
        have e := K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
        convert e using 1
        group
      obtain ⟨x, hx, -⟩ := hr _ hκ
      refine ⟨(QuotientGroup.mk c, x), ?_⟩
      simp only [φ]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      have e := hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx
      convert e using 1
      group
  haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2
  letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _
  have hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2)
      = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z))) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K')
      (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
    simp only [φ]
    rw [hu]
    push_cast
    have hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K' :=
      K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))
    have e := hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)
    rw [mul_assoc h, ← e]
    congr 1
    group
  let g : K' ⧸ M.subgroupOf K' → Γ ⧸ K := fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹
  have hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y)
      = ((Finset.univ.filter (fun b => g b = y)).card : ℂ) := by
    intro y
    have hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' =>
        h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y := by
      refine Finset.filter_congr fun b _ => ?_
      simp only [g]
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rw [QuotientGroup.eq, inv_inv]
    unfold cntFn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  have hsupp : (Function.support fun y : Γ ⧸ K =>
      cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g) := by
    intro y hy
    rw [Function.mem_support, hcnt] at hy
    by_contra hyn
    apply hy
    have e : Finset.univ.filter (fun b => g b = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))
    simp [e]
  have hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹
      = ∑ b, P (Quotient.out (g b))⁻¹ := by
    rw [Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hcnt, Nat.cast_smul_eq_nsmul]
  have hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹
    simp only [g]
    rw [hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]
    exact hP _ (K.inv_mem k.2) _ (Quotient.out b).2
  rw [hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z))))
    (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHomEx
section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem UpperTheory.Gal.LocalSmoothExtension.homEx_of :
    HomEx := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  have ext'' : ∀ {T : Over S₁} (u v : T ⟶ o₁''.A), u.left ≫ m''.φ = v.left ≫ m''.φ → u = v := by
    intro T u v h
    apply Over.OverMorphism.ext
    exact m''.cart.1.hom_ext h (by rw [Over.w u, Over.w v])
  have p' : ∀ (T : Over S₁) (x : T ⟶ o₁'.A), (pushHom m'.cart T x).left = x.left ≫ m'.φ :=
    fun _ _ => rfl
  have p'' : ∀ (T : Over S₁) (x : T ⟶ o₁''.A), (pushHom m''.cart T x).left = x.left ≫ m''.φ :=
    fun _ _ => rfl
  refine ⟨?_, fun ψ₁ ψ₂ h => ext'' ψ₁ ψ₂ h, ?_⟩
  · intro ψ hψ
    haveI := hψ
    have w : (m'.φ ≫ ψ.left) ≫ o''.A.hom = o₁'.A.hom ≫ f := by
      rw [Category.assoc, Over.w ψ, m'.cart.1.w]
    let ψ₁ : o₁'.A ⟶ o₁''.A :=
      Over.homMk (m''.cart.1.lift (m'.φ ≫ ψ.left) o₁'.A.hom w) (m''.cart.1.lift_snd _ _ w)
    have hψ₁ : ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left := m''.cart.1.lift_fst _ _ w
    refine ⟨ψ₁, ?_, hψ₁⟩
    apply isMonHom_of_mul
    intro T x y
    apply ext''
    have e : ∀ z : T ⟶ o₁'.A, pushHom m''.cart T (z ≫ ψ₁) = pushHom m'.cart T z ≫ ψ := by
      intro z
      apply Over.OverMorphism.ext
      rw [p'', Over.comp_left, Over.comp_left, p', Category.assoc, Category.assoc, hψ₁]
    rw [← p'', ← p'', map_mul, e, e, e, map_mul, mul_comp]
  · intro d
    let e : Over.mk (o₁'.A.hom ≫ f) ⟶ o'.A := pushHom m'.cart o₁'.A (𝟙 o₁'.A)
    have h1 : (𝟙 o₁'.A ^ d).left ≫ m'.φ = (e ^ d).left := by
      rw [← p', map_pow]
    have h2 : m'.φ ≫ (𝟙 o'.A ^ d).left = (e ^ d).left := by
      have : e ≫ 𝟙 o'.A ^ d = e ^ d := by rw [comp_pow, Category.comp_id]
      rw [← this, Over.comp_left, p', Over.id_left, Category.id_comp]
    rw [h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLegBc
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down exists_gObjMap_pull spMap_comp')
open UpperTheory.Gal.Int.Geo (IsTrans)
open UpperTheory.Gal.LocalSmoothExtension

private theorem objMap_along {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj b N s'} {o : GObj b N s} {f g : S' ⟶ S}
    (e : f = g) (n : GObjMap o' o f) : ∃ n' : GObjMap o' o g, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

theorem UpperTheory.Gal.LocalSmoothExtension.legBc_of :
    MapEq → TransPull → LegBc := by
  intro hME hTP p _ D G L R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N N' M M' P P' f f' hf hf' m m' h π o ψ φ hπ hψ
  have hw : (f' ≫ π) ≫ M.s = P'.s ≫ spMap τ := by
    rw [Category.assoc, hπ]
    exact hf'.w
  obtain ⟨π₁, hπf, hπs⟩ : ∃ π₁ : P'.X ⟶ P.X, π₁ ≫ f = f' ≫ π ∧ π₁ ≫ P.s = P'.s :=
    ⟨hf.lift (f' ≫ π) P'.s hw, hf.lift_fst _ _ _, hf.lift_snd _ _ _⟩
  obtain ⟨o₁, ⟨φ₁⟩⟩ : ∃ o₁ : GObj gb₂ N P'.s, Nonempty (GObjMap o₁ P.univ π₁) := by
    have key := exists_gObjMap_pull π₁ P.univ
    rw [hπs] at key
    exact key
  let d₁ : GObj gb₁ N (P'.s ≫ spMap τ) := down hρ ht rfl o₁
  let φd : GObjMap d₁ (down hρ ht rfl P.univ) π₁ :=
    ⟨φ₁.φ, φ₁.φ₂, φ₁.cart, φ₁.sq, φ₁.act, φ₁.pol, φ₁.eta⟩
  obtain ⟨n, hn⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ (down hρ ht rfl P.univ) M.univ π₁ f m).1 φd
  obtain ⟨n', hn'⟩ := objMap_along hπf n
  obtain ⟨m'', hm''⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ o M.univ f' π φ).2 n'
  obtain ⟨ψ₁, hψ₁, hT⟩ := hTP p D G L R₁ gb₁ N N' _ _ M'.s (P'.s ≫ spMap τ) f' hf'.w M'.univ o
    (down hρ ht rfl P'.univ) d₁ m' m'' h ψ hψ
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := hT
  refine ⟨π₁, o₁, ψ₁, φ₁, hπs, ⟨t₁, t₂, t₃, t₄, fun k _ _ t β hβ => ?_⟩, hπf, ?_⟩
  · exact t₅ k t (β.comp τ) (by rw [spMap_comp', ← Category.assoc, hβ])
  · have e : φ₁.φ ≫ m.φ = m''.φ ≫ φ.φ := by
      rw [hm'', hn', hn]
      rfl
    calc (ψ₁.left ≫ φ₁.φ) ≫ m.φ = ψ₁.left ≫ φ₁.φ ≫ m.φ := Category.assoc _ _ _
      _ = ψ₁.left ≫ m''.φ ≫ φ.φ := congrArg (fun z => ψ₁.left ≫ z) e
      _ = (ψ₁.left ≫ m''.φ) ≫ φ.φ := (Category.assoc _ _ _).symm
      _ = m'.φ ≫ ψ.left ≫ φ.φ := by rw [hψ₁, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMapEq
section
open UpperTheory.Gal.LocalSmoothExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory.UPel.HT.MapComp

theorem UpperTheory.Gal.LocalSmoothExtension.mapEq_of :
    MapEq := by
  intro G R _ _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₂
  refine ⟨fun m₁ => ?_, fun m => ?_⟩
  · refine ⟨⟨m₁.φ ≫ m₂.φ, m₁.φ₂ ≫ m₂.φ₂, IsGrpPullback.comp m₁.cart m₂.cart,
      isSquare_comp m₁.sq m₂.sq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
        (lbIso_pull_comp m₂.pol m₁.φ₂ rfl), fun y => ?_⟩, rfl⟩
    · rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
    · rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]
  · have hw : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by
      rw [Category.assoc]; exact m.cart.1.w
    let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) hw
    have h₁ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
    obtain ⟨φ₂, hsq⟩ := exists_isSquare h₂
    have h₃ : φ₂ ≫ m₂.φ₂ = m.φ₂ := by
      have := isSquare_comp hsq m₂.sq
      rw [h₁] at this
      exact isSquare_unique this m.sq
    have hc : IsGrpPullback o₁.A o₂.A f φ :=
      IsGrpPullback.cancel m₂.cart (by rw [h₁]; exact m.cart) h₂
    refine ⟨⟨φ, φ₂, hc, hsq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
        (lbIso_pull_comp m₂.pol φ₂ h₃.symm).symm, fun y => ?_⟩, h₁⟩
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.act, Category.assoc, m₂.act, ← Category.assoc, h₁]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.eta, Category.assoc, Category.assoc, m₂.eta]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
        simp

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PModelBc
section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.Gen.BaseChange

theorem UpperTheory.Gal.LocalSmoothExtension.modelBc_of :
    MapEq → ModelBc := by
  intro hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M
  obtain ⟨o', ⟨mo⟩⟩ := exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ
  let U : GObj gb₂ N (pullback.snd M.s (spMap τ)) := up hρ ht pullback.condition.symm o'
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'),
      ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j) := by
    intro S s' o
    let u : GObj gb₁ N (s' ≫ spMap τ) := down hρ ht rfl o
    obtain ⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩ := M.rep S _ u
    let j : S ⟶ pullback M.s (spMap τ) := pullback.lift a s' ha
    have j₁ : j ≫ pullback.fst M.s (spMap τ) = a := pullback.lift_fst _ _ _
    have j₂ : j ≫ pullback.snd M.s (spMap τ) = s' := pullback.lift_snd _ _ _
    obtain ⟨mj, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)
    have mj' : GObjMap o U j := ⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩
    refine ⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩
    rintro j' ⟨h₂, ⟨m'⟩⟩
    have m'' : GObjMap u o' j' := ⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩
    obtain ⟨n, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''
    have e : j' ≫ pullback.fst M.s (spMap τ) = a :=
      hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩
    apply pullback.hom_ext
    · rw [e, j₁]
    · rw [h₂, j₂]
  refine ⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ),
    IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolPull
section
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private theorem isSquare_square_compatible_homs {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A']
    [IsCommMonObj A'] (ψ : A ⟶ A') : Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.LocalSmoothExtension.polPull_of :
    PolPull := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hc c ⟨h⟩
  letI := o'.grp
  letI := o'.comm
  letI := o''.grp
  letI := o''.comm
  letI := o₁'.grp
  letI := o₁'.comm
  letI := o₁''.grp
  letI := o₁''.comm
  have hsq : Hecke.sq2 ψ₁ ≫ m''.φ₂ = m'.φ₂ ≫ Hecke.sq2 ψ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp (isSquare_square_compatible_homs ψ₁) m''.sq)
    rw [hc]
    exact MapComp.isSquare_comp m'.sq (isSquare_square_compatible_homs ψ)
  have hp : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
  have hp₁ : (Hecke.lbPow o₁'.P c).IsLB := LB.isLB_linComb o₁'.isLB _ _
  have hq : (o''.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o''.isLB _
  have hA := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
  have hB := (GlobalTheory.CechPic.cls_eq_iff o₁''.isLB (pull_isLB o''.isLB m''.φ₂)).2 m''.pol
  have hC := (GlobalTheory.CechPic.cls_eq_iff hp hq).2 h
  refine ⟨(GlobalTheory.CechPic.cls_eq_iff hp₁ (pull_isLB o₁''.isLB _)).1 ?_⟩
  rw [GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB, hA, GlobalTheory.CechPic.cls_pull o'.isLB,
    GlobalTheory.CechPic.cls_pull o₁''.isLB, hB, GlobalTheory.CechPic.cls_pull o''.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
    GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o''.isLB (Hecke.sq2 ψ) hq, ← hC,
    GlobalTheory.BirigidPow.cls_lbPow o'.isLB, map_nsmul]
end

