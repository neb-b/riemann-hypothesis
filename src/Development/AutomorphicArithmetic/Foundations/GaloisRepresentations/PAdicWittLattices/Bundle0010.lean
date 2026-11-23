module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
public import Development.EtaleCohomology.WeilConjectures.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrBase :
    FEtBasic → SplitsBasic → GalClosD → TrBase.{u} := by
  intro hF hS hC B R _ T hT P Y Z' Z p q p' q' v s' s g d hv hg hq' hpb hs tr tr' htr htr' x
  haveI : IsFinite s := hs.1
  haveI : Etale s := hs.2.1
  obtain ⟨W, c, G, _, _, a, σ, hgal, hspl⟩ := hC s' d (hF.1 v s' s g d hpb hs)
  have hσs : ∀ j, σ j ≫ s' = c := hspl.1
  have hσ' : ∀ j, σ j ≫ q' = c ≫ p' := fun j => by
    rw [← hq', ← Category.assoc, hσs j]
  have hσv : ∀ j, (σ j ≫ v) ≫ q = c ≫ p' := fun j => by
    rw [Category.assoc, hv, hσ' j]
  have hcg : (c ≫ g) ≫ p = c ≫ p' := by rw [Category.assoc, hg]
  have hspl2 : Splits s (c ≫ g) (fun j => σ j ≫ v) :=
    (hS.2 v s' s g hpb c (Fin d) σ hσs).1 hspl
  apply hT.inj p' (c ≫ p') c rfl G a hgal
  rw [← T.pull_comp c g rfl hg hcg, htr W (c ≫ p') (c ≫ g) hcg (Fin d) (fun j => σ j ≫ v) hσv hspl2 x,
    htr' W (c ≫ p') c rfl (Fin d) σ hσ' hspl]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact T.pull_comp (σ j) v (hσ' j) hv (hσv j) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrPushM :
    FEtBasic → SplitsBasic → SplitsComp → MultiSplit → FEtInj.{u} → TrPushM.{u} := by
  intro hF hSB hSC hMS hInj B R _ T hT Y P Z p q r κ s d m hκ hs hd hm tr tr' htr htr' x
  haveI : IsFinite s := hd.1
  haveI : Etale s := hd.2.1
  haveI : IsFinite κ := hm.1
  haveI : Etale κ := hm.2.1
  obtain ⟨W1, c1, e1, he1, hc1, hτ0⟩ := hMS 1 (fun _ => P) (fun _ => s) (fun _ => d) (fun _ => hd)
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin d → (W1 ⟶ P), Splits s c1 τ := hτ0 0
  have hPb : ∀ i : Fin d, FEt (pullback.snd κ (τ i)) m := fun i =>
    hF.1 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) m
      (IsPullback.of_hasPullback κ (τ i)) hm
  obtain ⟨W2, c2, e2, he2, hc2, hρ0⟩ :=
    hMS d (fun i => pullback κ (τ i)) (fun i => pullback.snd κ (τ i)) (fun _ => m) hPb
  have hρ1 : ∀ i : Fin d, ∃ ρ : Fin m → (W2 ⟶ pullback κ (τ i)),
      Splits (pullback.snd κ (τ i)) c2 ρ := hρ0
  choose ρ hρ using hρ1
  have key : ∀ i j, (ρ i j ≫ pullback.fst κ (τ i)) ≫ κ = c2 ≫ τ i := fun i j => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, (hρ i).1 j]
  have hsκ : ∀ i, Splits κ (c2 ≫ τ i) (fun j => ρ i j ≫ pullback.fst κ (τ i)) := fun i =>
    (hSB.2 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i)
      (IsPullback.of_hasPullback κ (τ i)) c2 (Fin m) (ρ i) (hρ i).1).1 (hρ i)
  have hss : Splits s (c2 ≫ c1) (fun i => c2 ≫ τ i) := hSB.1 s c1 (Fin d) τ c2 hτ
  have hcomp := hSC κ s (c2 ≫ c1) (Fin d) (Fin m) (fun i => c2 ≫ τ i)
    (fun i j => ρ i j ≫ pullback.fst κ (τ i)) hss hsκ
  have hfc : FEt (c2 ≫ c1) (e1 * e2) := hF.2.1 c2 c1 e1 e2 hc2 hc1
  have hστ : ∀ i, (c2 ≫ τ i) ≫ q = (c2 ≫ c1) ≫ p := fun i => by
    rw [← hs]
    simp only [Category.assoc]
    rw [← Category.assoc (τ i) s p, hτ.1 i]
  have hσ' : ∀ y : Fin d × Fin m, (ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) ≫ r = (c2 ≫ c1) ≫ p :=
    fun y => by
      rw [← hκ, ← Category.assoc, key]
      exact hστ y.1
  have move : ∀ (f : W2 ⟶ Y) (g : W2 ⟶ P) (hf : f ≫ r = (c2 ≫ c1) ≫ p)
      (hg : g ≫ q = (c2 ≫ c1) ≫ p), f ≫ κ = g → T.pull f hf (T.pull κ hκ x) = T.pull g hg x := by
    intro f g hf hg e
    subst e
    exact (T.pull_comp f κ hf hκ hg x).symm
  apply hInj T hT p ((c2 ≫ c1) ≫ p) (c2 ≫ c1) rfl (e1 * e2) (Nat.mul_pos he1 he2) hfc
  rw [htr' W2 _ (c2 ≫ c1) rfl (Fin d × Fin m) (fun y => ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) hσ' hcomp]
  rw [map_smul, htr W2 _ (c2 ≫ c1) rfl (Fin d) (fun i => c2 ≫ τ i) hστ hss]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun j _ => move _ _ (hσ' (i, j)) (hστ i) (key i j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul R m _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTwGal :
    TwSplit → TwGal := by
  intro hS B G _ X m j b hnorm
  classical
  haveI hN : ((X.K m).subgroupOf (X.K j)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hnorm g g.2 n hn⟩
  haveI : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx m j)
  have admr : ∀ c : X.K j ⧸ (X.K m).subgroupOf (X.K j), X.admitted m m ((c.out : X.K j) : G)⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hnorm _ (inv_mem c.out.2) u hu⟩
  have uniq : ∀ k ∈ X.K j, ∃! c : X.K j ⧸ (X.K m).subgroupOf (X.K j),
      k * (((c.out : X.K j) : G))⁻¹⁻¹ ∈ X.K m := by
    intro k hk
    refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
      simp only [inv_inv]
      rw [hu]
      have hu' : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
      simpa [mul_assoc] using hu'
    · intro c hc
      simp only [inv_inv] at hc
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_inv_rev] using inv_mem hc
  have trc : ∀ (g1 g2 : G) (e : g1 = g2) (p1 : X.admitted m m g1) (p2 : X.admitted m m g2),
      X.tr m m g1 p1.1 p1.2 = X.tr m m g2 p2.1 p2.2 := by
    intro g1 g2 e p1 p2
    subst e
    rfl
  have tl : ∀ (g k : G) (hg : X.admitted m m g) (hk : k ∈ X.K m) (hkg : X.admitted m m (k * g)),
      X.tr m m (k * g) hkg.1 hkg.2 = X.tr m m g hg.1 hg.2 := by
    intro g k hg hk hkg
    rw [← X.tr_mul m m m g k hg.1 hg.2 (X.K_le m k hk) (X.tower_admissible_self hk).2 hkg.1 hkg.2,
      X.tr_self m k _ _ hk, Category.comp_id]
  refine ⟨X.K j ⧸ (X.K m).subgroupOf (X.K j), inferInstance, inferInstance,
    fun c => ((c.out : X.K j) : G)⁻¹, admr, fun c => inv_mem c.out.2, uniq, ?_⟩
  unfold GlobalTheory.GalV.IsGalois
  refine ⟨X.fin m j b.1 b.2, X.etale m j b.1 b.2, X.onto m j b.1 b.2, ?_, ?_,
    hS X m m j b b le_rfl hnorm _ _ admr (fun c => inv_mem c.out.2) uniq⟩
  · have h1 : ((1 : X.K j ⧸ (X.K m).subgroupOf (X.K j)).out : G) ∈ X.K m :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1))
    exact X.tr_self m _ _ _ (inv_mem h1)
  · intro g g'
    set w : X.K j := ((g.out : X.K j) * g'.out)⁻¹ * (g * g').out with hwdef
    have hw : w ∈ (X.K m).subgroupOf (X.K j) := by
      rw [hwdef, ← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']
    have hw' : ((w : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp hw
    have e : (((g * g').out : X.K j) : G)⁻¹ =
        ((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) := by
      simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hA : X.admitted m m ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) :=
      Tower.admitted.mul (admr g) (admr g')
    have hB : X.admitted m m (((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹)) :=
      Tower.admitted.mul hA (X.tower_admissible_self (inv_mem hw'))
    exact ((trc _ _ e (admr (g * g')) hB).trans (tl _ _ hA (inv_mem hw') hB)).trans
      (X.tr_mul m m m _ _ (admr g).1 (admr g).2 (admr g').1 (admr g').2 hA.1 hA.2).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem tr_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k : G} (hk : k ∈ X.K j)
    (a : X.admitted i j h) (p q) : X.tr i j (k * h) p q = X.tr i j h a.1 a.2 := by
  rw [← X.tr_mul i j j h k a.1 a.2 (X.K_le j k hk) (X.tower_admissible_self hk).2 p q,
    X.tr_self j k _ _ hk, Category.comp_id]

private theorem tower_tr_eq_of_eq_mul_of_mem_K {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k g : G}
    (hk : k ∈ X.K j) (a : X.admitted i j h) (hg : g = k * h) (p q) : X.tr i j g p q = X.tr i j h a.1 a.2 := by
  subst hg
  exact tr_left X hk a p q

private theorem tower_tr_comp_tr_eq_tr_mul {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j m : X.ι} {h h' : G}
    (p : h ∈ X.Δ) (q : ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j) (p' : h' ∈ X.Δ)
    (q' : ∀ u ∈ X.K j, h' * u * h'⁻¹ ∈ X.K m) :
    X.tr i j h p q ≫ X.tr j m h' p' q' =
      X.tr i m (h' * h) (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).1
        (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).2 :=
  X.tr_mul _ _ _ _ _ _ _ _ _ _ _

theorem UpperTheory.Gal.G3.pTwSplit :
    SplitsPts → TwSplit := by
  intro hS B G _ X m i j a b hmi hnorm J _ r c hr huniq
  have hij : ∀ u ∈ X.K i, u ∈ X.K j := fun u hu => by simpa using a.2 u hu
  have hmj : ∀ u ∈ X.K m, u ∈ X.K j := fun u hu => by simpa using b.2 u hu
  have Am : ∀ g ∈ X.K j, X.admitted m m g := fun g hg => ⟨X.K_le j g hg, fun u hu => hnorm g hg u hu⟩
  have hcomp : ∀ x, X.tr m i (r x) (c x).1 (c x).2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    intro x
    rw [X.tr_mul m i j (r x) 1 (c x).1 (c x).2 a.1 a.2 ((c x).mul a).1 ((c x).mul a).2]
    exact tower_tr_eq_of_eq_mul_of_mem_K X (hr x) b (by simp) _ _
  have U : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (x1 x2 : J),
      x ≫ X.tr m i (r x1) (c x1).1 (c x1).2 = x ≫ X.tr m i (r x2) (c x2).1 (c x2).2 → x1 = x2 := by
    intro Ω _ _ x x1 x2 h12
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    have e1 : (x ≫ X.tr m m (r x1) (Am _ (hr x1)).1 (Am _ (hr x1)).2) ≫ X.tr m i 1 p1.1 p1.2
        = (x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2) ≫ X.tr m i 1 p1.1 p1.2 := by
      rw [Category.assoc, Category.assoc, tower_tr_comp_tr_eq_tr_mul, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x1) (rfl : (1:G) * r x1 = 1 * r x1),
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x2) (rfl : (1:G) * r x2 = 1 * r x2)]
      exact h12
    obtain ⟨k, hki, a', b', hk⟩ := X.trans m i p1.1 p1.2
      (fun k hk u hu => hnorm k (hij k hk) u hu) Ω _ _ e1
    have hkj := hij k hki
    have e2 : x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2
        = x ≫ X.tr m m (k * r x1) (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2 := by
      rw [hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul]
    have hinv : (r x2)⁻¹ ∈ X.K j := inv_mem (hr x2)
    have hg : (r x2)⁻¹ * (k * r x1) ∈ X.K j := mul_mem hinv (mul_mem hkj (hr x1))
    have hfix : x ≫ X.tr m m _ (Am _ hg).1 (Am _ hg).2 = x := by
      rw [← X.tr_mul m m m (k * r x1) (r x2)⁻¹ (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2
        (Am _ hinv).1 (Am _ hinv).2, ← Category.assoc, ← e2, Category.assoc,
        X.tr_mul m m m (r x2) (r x2)⁻¹ (Am _ (hr x2)).1 (Am _ (hr x2)).2 (Am _ hinv).1 (Am _ hinv).2
          (Am _ (mul_mem hinv (hr x2))).1 (Am _ (mul_mem hinv (hr x2))).2,
        X.tr_self m _ _ _ (by simp), Category.comp_id]
    have hgm := X.free m j (fun u hu => hmj u hu) _ hg (Am _ hg).1 (Am _ hg).2 Ω x hfix
    have hk0 : k * r x1 ∈ X.K j := mul_mem hkj (hr x1)
    apply (huniq _ hk0).unique
    · simpa using hki
    · have := (c x2).2 _ hgm
      convert this using 1
      group
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (y : sp Ω ⟶ X.Z i),
      y ≫ X.tr i j 1 a.1 a.2 = x ≫ X.tr m j 1 b.1 b.2 → ∃! x0, x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
    intro Ω _ _ x y hxy
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    haveI := X.fin m i p1.1 p1.2
    obtain ⟨v, hv⟩ := (X.onto m i p1.1 p1.2).surj (UpperTheory.Gal.TranscendenceTraces.pt (X := X.Z i) (Ω := Ω) y)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds (X.tr m i 1 p1.1 p1.2) Ω y v hv
    have hzj : x ≫ X.tr m j 1 b.1 b.2 = z ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hxy, ← hz, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K j)) b (rfl : (1:G) * 1 = 1 * 1)]
    obtain ⟨k, hkj, a', b', hk⟩ := X.trans m j b.1 b.2 hnorm Ω x z hzj
    obtain ⟨x0, hx0, -⟩ := huniq k hkj
    have ex : x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
      rw [← hz, hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X hx0 (c x0) (show (1:G) * k = k * (r x0)⁻¹ * r x0 by group)]
    exact ⟨x0, ex, fun x2 h2 => U Ω x x2 x0 (h2.trans ex.symm)⟩
  haveI := X.fin i j a.1 a.2
  haveI := X.etale i j a.1 a.2
  exact hS _ _ J _ hcomp hpts
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pullIdentity_move {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} {r r' : W ⟶ B} (e : r = r') (c : W ⟶ Z) {J : Type} [Fintype J]
    (t : J → (W ⟶ Z')) (y : T.H p) (x : T.H p') (h : c ≫ p = r) (h' : c ≫ p = r')
    (k : ∀ j, t j ≫ p' = r) (k' : ∀ j, t j ≫ p' = r')
    (H : T.pull c h y = ∑ j, T.pull (t j) (k j) x) :
    T.pull c h' y = ∑ j, T.pull (t j) (k' j) x := by
  subst e
  exact H

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e
  rfl

private theorem bcMap_comp' {B B' X Y V : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : V ⟶ B'}
    (f : Y ⟶ X) (f' : V ⟶ Y) (h : f ≫ p = q) (h' : f' ≫ q = r) (h'' : (f' ≫ f) ≫ p = r) :
    bcMap g (f' ≫ f) h'' = bcMap g f' h' ≫ bcMap g f h := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g f' h'), bcMap_fst,
      Category.assoc]
  · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]

theorem UpperTheory.Gal.G3.pOpBc :
    BcSplits → BcGal → OpBc.{u} := by
  intro hS hG B B' R _ T g Z Y Z' p q p' s _ _ t hs ht A hA
  obtain ⟨W, c, G, _, _, a, J, _, σ, hh, hgal, hspl, hsum⟩ := hA
  have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
    rw [← hs, ← Category.assoc, hspl.1 j]
  have ha : ∀ x, a x ≫ (c ≫ p) = c ≫ p := fun x => by
    rw [← Category.assoc, hgal.2.2.2.2.2.1 x]
  refine ⟨pullback (c ≫ p) g, bcMap g c rfl, G, inferInstance, inferInstance,
    fun x => bcMap g (a x) (ha x), J, inferInstance, fun j => bcMap g (σ j) (hσ j), ?_,
    hG g p (c ≫ p) c rfl G a ha hgal, (hS g p q (c ≫ p) s hs c rfl J σ hσ).2.2 hspl, ?_⟩
  · intro j
    rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  · intro x
    have e : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j ≫ t) (hh j)) (bcMap_snd g _ (hh j)) x := hsum x
    have e2 : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j) (hσ j) ≫ bcMap g t ht)
          (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x := by
      rw [e]
      exact Finset.sum_congr rfl fun j _ =>
        pull_congr T (bcMap_comp' g t (σ j) ht (hσ j) _) _ _ x
    exact pullIdentity_move T (bcMap_snd g c rfl).symm _ _ _ _ _ _ _ _ e2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
end

