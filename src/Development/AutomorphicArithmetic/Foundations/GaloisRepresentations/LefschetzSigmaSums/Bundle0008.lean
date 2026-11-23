module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPowComp
section
open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

theorem UpperTheory.Gal.LocalSmoothExtension.powComp_of :
    PowComp := by
  intro S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k
  subst hfg
  subst hφχ
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      GlobalTheory.KS.PowPB.powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaFEt
section
open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaSplit
section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaSplit_of :
    SigmaFEt → UpperTheory.Gal.G3.SplitsPts → UpperTheory.Gal.G3.PtsOfSplits → SigmaSplit := by
  intro hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs
  obtain ⟨hF1, hF2⟩ := hF Y Z s I
  obtain ⟨hsc, hiso⟩ := hs
  have hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω) := fun Ω _ =>
    inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y),
      ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y := by
    intro Ω _ y
    haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω
    obtain ⟨p⟩ := hne Ω
    obtain ⟨⟨i, a⟩, ha⟩ := (sigmaMk (fun _ : I => Y)).surjective (y.base p)
    rw [sigmaMk_mk] at ha
    refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨a, by rw [Subsingleton.elim q p]; exact ha⟩
  refine hSP _ c (I × Δ) _ ?_ ?_
  · intro z
    simp [hsc]
  · intro Ω _ _ x y hy
    obtain ⟨i, y', rfl⟩ := hpt Ω y
    have hy' : y' ≫ s = x ≫ c := by simpa using hy
    obtain ⟨δ, hδ, hδu⟩ := hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'
    refine ⟨(i, δ), ?_, ?_⟩
    · show x ≫ (σ δ ≫ _) = _
      rw [← hδ, Category.assoc]
    · rintro ⟨i', δ'⟩ h
      change x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h
      by_cases hii : i' = i
      · subst hii
        have hx : x ≫ σ δ' = y' := by
          rw [← Category.assoc] at h
          exact (cancel_mono _).1 h
        rw [hδu δ' hx]
      · haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y')
          ⟨by rw [Category.assoc]; exact h⟩ hii
        obtain ⟨p⟩ := hne Ω
        exact isEmptyElim p
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTatePull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.tatePull_of :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R]
      (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
      (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S)
      (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
      (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : UpperTheory.Gal.Int.Geo.TIso o (t ≫ f)),
      ∃ I₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t, ∀ n y,
        (I₁.ev n y).left ≫ m.φ = (I.ev n y).left := by
  intro p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I
  letI := o.grp
  letI := o₁.grp
  letI := o.comm
  have hl : ∀ x : Over.mk t ⟶ o₁.A,
      Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ := fun _ => rfl
  let E := MulEquiv.ofBijective (pushHom m.cart (Over.mk t))
    ⟨push_injective m.cart _, push_surjective m.cart _⟩
  have key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q := fun q => by
    rw [← hl]
    exact congrArg Over.Hom.left (E.apply_symm_apply q)
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n y => E.symm (I.ev n y),
            add := fun n x y => by simp only [I.add, map_mul],
            lin := fun n c x => ?_,
            ker := fun n hn x => by
              rw [← I.ker n hn x]
              exact E.symm.map_eq_one_iff,
            onto := fun n hn q => ?_,
            tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],
            isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩
  · have h1 := push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))
    have h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x := E.apply_symm_apply _
    rw [h2] at h1
    apply E.injective
    rw [E.apply_symm_apply, I.lin]
    exact h1.symm
  · constructor
    · intro hq
      obtain ⟨x, hx⟩ := (I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])
      exact ⟨x, by rw [hx, E.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]
  · exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _)
      m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2
      (I.isom n hn x y)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTransPull
section
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (IsTrans TIso)

private theorem pt_ext {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S₁ T : Scheme.{0}} {s : S ⟶ Sp R} {s₁ : S₁ ⟶ Sp R} {f : S₁ ⟶ S} {o : GObj b N s} {o₁ : GObj b N s₁}
    (m : GObjMap o₁ o f) {t : T ⟶ S₁} (x y : Over.mk t ⟶ o₁.A) (h : x.left ≫ m.φ = y.left ≫ m.φ) : x = y := by
  letI := o.grp
  letI := o₁.grp
  apply GlobalTheory.SiegelPull.push_injective m.cart (Over.mk t)
  exact Over.OverMorphism.ext h

theorem UpperTheory.Gal.LocalSmoothExtension.transPull_of :
    HomEx → PolPull → TatePull → TransPull := by
  intro hHom hPol hTate p _ D G L R _ _ b N N' S S₁ s s₁ f hfs o' o'' o₁' o₁'' m' m'' h ψ hT
  obtain ⟨hψ, hact, ⟨ψ', d, hψ', hact', hc1, hc2, hd⟩, hpolc, hgeo⟩ := hT
  obtain ⟨c, hcp, hpol, hrest⟩ := hpolc
  letI := o'.grp
  letI := o''.grp
  letI := o₁'.grp
  letI := o₁''.grp
  obtain ⟨hlift, huniq, hpow⟩ := hHom D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  obtain ⟨hlift', huniq', hpow'⟩ := hHom D.toG R b N' N S S₁ s s₁ f o'' o' o₁'' o₁' m'' m'
  have hu₁ := (hHom D.toG R b N' N' S S₁ s s₁ f o' o' o₁' o₁' m' m').2.1
  have hu₂ := (hHom D.toG R b N N S S₁ s s₁ f o'' o'' o₁'' o₁'' m'' m'').2.1
  obtain ⟨ψ₁, hψ₁, hcomm⟩ := hlift ψ hψ
  obtain ⟨ψ₁', hψ₁', hcomm'⟩ := hlift' ψ' hψ'
  refine ⟨ψ₁, hcomm, hψ₁, ?_, ⟨ψ₁', d, hψ₁', ?_, ?_, ?_, hd⟩,
    ⟨c, hcp, hPol D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hcomm c hpol, hrest⟩, ?_⟩
  · intro e
    apply huniq
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm, hcomm, reassoc_of% (m'.act e),
      m'.act e, m''.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact e]
  · intro e
    apply huniq'
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm', hcomm', reassoc_of% (m''.act e),
      m''.act e, m'.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact' e]
  · apply hu₁
    simp only [Over.comp_left, Category.assoc, hcomm', reassoc_of% hcomm, hpow d, ← hc1]
  · apply hu₂
    simp only [Over.comp_left, Category.assoc, hcomm, reassoc_of% hcomm', hpow' d, ← hc2]
  · intro k _ _ t β ht
    have htf : (t ≫ f) ≫ s = spMap β := by rw [Category.assoc, hfs, ht]
    obtain ⟨I', I'', h1, h2, h3⟩ := hgeo k (t ≫ f) β htf
    obtain ⟨I₁', k₁⟩ := hTate p D R b N' S S₁ s s₁ f o' o₁' m' k t I'
    obtain ⟨I₁'', k₂⟩ := hTate p D R b N S S₁ s s₁ f o'' o₁'' m'' k t I''
    have hu : ∀ {X : Scheme} (g : Sp k ⟶ X), Over.Hom.left (toUnit (Over.mk g)) = g := by
      intro X g
      simpa using Over.w (toUnit (Over.mk g))
    refine ⟨I₁', I₁'', fun y => ?_, fun y => ?_, fun n hn hp x y => ?_⟩
    · apply pt_ext m'
      simp only [Over.comp_left, Category.assoc, m'.eta, k₁, ← h1, hu]
    · apply pt_ext m''
      simp only [Over.comp_left, Category.assoc, m''.eta, k₂, ← h2, hu]
    · refine Iff.trans ?_ (h3 n hn hp x y)
      have e : Over.Hom.left (I₁'.ev n x ≫ ψ₁) ≫ m''.φ = Over.Hom.left (I'.ev n x ≫ ψ) := by
        rw [Over.comp_left, Category.assoc, hcomm, ← Category.assoc, k₁ n x, Over.comp_left]
      constructor
      · intro hxy
        apply Over.OverMorphism.ext
        rw [← e, hxy]
        exact k₂ n y
      · intro hxy
        apply pt_ext m''
        rw [e, hxy]
        exact (k₂ n y).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr
section
open UpperTheory.Gal.LocalSmoothExtension

open CategoryTheory Limits AlgebraicGeometry in
private theorem pull_congr' {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q) (hf' : f' ≫ p = q) (x : Θ.H p) :
    Θ.pull f hf x = Θ.pull f' hf' x := by
  subst e
  rfl


open CategoryTheory Limits AlgebraicGeometry in
private theorem pull_base {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} (c : W ⟶ Z) {J : Type} [Fintype J] (f : J → (W ⟶ Z')) (A : Θ.H p' →ₗ[R] Θ.H p)
    (r : W ⟶ B) (hc : c ≫ p = r) (hf : ∀ j, f j ≫ p' = r)
    (H : ∀ x, Θ.pull c hc (A x) = ∑ j, Θ.pull (f j) (hf j) x) (hf' : ∀ j, f j ≫ p' = c ≫ p) (x : Θ.H p') :
    Θ.pull c rfl (A x) = ∑ j, Θ.pull (f j) (hf' j) x := by
  subst hc
  exact H x


open CategoryTheory Limits AlgebraicGeometry in
private theorem op_core (hFn : CntFn) (hSum : CntSum) (hSig : SigmaFEt) (hSpl : SigmaSplit)
    (hGal : UpperTheory.Gal.G3.TwGal) (hEx : UpperTheory.Gal.G3.HopEx.{0})
    {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : UpperTheory.Gal.G3.Tower B Γ) (i m : X.ι) (K K' M : Subgroup Γ) (h : Γ)
    (hK : X.K i = K) (hM : X.K m = M) (hMK : M ≤ K) (hKK : K ≤ K')
    (hn : ∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) (hidx : M.relIndex K' ≠ 0)
    (hadm : ∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) (hΔ : ∀ k ∈ K', h * k ∈ X.Δ)
    (a1 : (1 : Γ) ∈ X.Δ) (b1 : ∀ u ∈ X.K m, (1 : Γ) * u * 1⁻¹ ∈ X.K i)
    (aT : ∀ c : K' ⧸ K.subgroupOf K', h * (c.out : Γ) ∈ X.Δ)
    (bT : ∀ c : K' ⧸ K.subgroupOf K', ∀ u ∈ X.K m, h * (c.out : Γ) * u * (h * (c.out : Γ))⁻¹ ∈ X.K i) :
    X.IsFn i (cntFn K K' M h) ∧
    IsFinite (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    Etale (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    ∀ Θ : UpperTheory.Gal.G3.Th.{0} B ℂ, Θ.Good → Θ.IsOp (X.q i) (X.q i)
      (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1)
      (Sigma.desc fun c : K' ⧸ K.subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c))
      (X.hecke Θ i (cntFn K K' M h)) := by
  subst hK hM
  have hcnt := hFn Γ (X.K i) K' (X.K m) h hKK hn hidx hadm
  have hIsFn : X.IsFn i (cntFn (X.K i) K' (X.K m) h) := by
    refine ⟨fun k hk g => hcnt.1 k hk g, fun g hg => ?_, hcnt.2.2⟩
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact X.Δ.mul_mem (X.K_le i k hk) (hΔ c hc)
  have hne : (X.K i).relIndex K' ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_of_le_left K' hMK
    rw [h0] at hd
    exact hidx (Nat.eq_zero_of_zero_dvd hd)
  haveI : ((X.K i).subgroupOf K').FiniteIndex := ⟨hne⟩
  haveI : IsFinite (X.tr m i 1 a1 b1) := X.fin m i a1 b1
  haveI : Etale (X.tr m i 1 a1 b1) := X.etale m i a1 b1
  have hsig := hSig (X.Z m) (X.Z i) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
  refine ⟨hIsFn, hsig.1, hsig.2, fun Θ hΘ => ?_⟩
  obtain ⟨Γ₀, _, _, r, cadm, hr, huq, hgal⟩ :=
    hGal X m i ⟨a1, b1⟩ (fun k hk u hu => hn k (hKK hk) u hu)
  letI : Fintype Γ₀ := Fintype.ofFinite Γ₀
  letI : Fintype (K' ⧸ (X.K i).subgroupOf K') := Fintype.ofFinite _
  have HarishChandraLabels : ∀ c ∈ K', X.admitted m i (h * c) := fun c hc => ⟨hΔ c hc, fun u hu => hadm c hc u hu⟩
  have adm : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀, X.admitted m i (h * (z.1.out : Γ) * r z.2) :=
    fun z => UpperTheory.Gal.G3.Tower.admitted.mul (cadm z.2) (HarishChandraLabels _ z.1.out.2)
  have ecomp : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀,
      (X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
          Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1) ≫
        Sigma.desc (fun c : K' ⧸ (X.K i).subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c)) =
      X.tr m i (h * (z.1.out : Γ) * r z.2) (adm z).1 (adm z).2 := by
    intro z
    rw [Category.assoc, Sigma.ι_desc]
    exact X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hspl := hSpl (X.Z m) (X.Z i) (X.Z m) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
    (X.tr m i 1 a1 b1) Γ₀ (fun x => X.tr m m (r x) (cadm x).1 (cadm x).2) hgal.2.2.2.2.2
  refine ⟨X.Z m, X.tr m i 1 a1 b1, Γ₀, inferInstance, inferInstance,
    fun x => X.tr m m (r x) (cadm x).1 (cadm x).2, (K' ⧸ (X.K i).subgroupOf K') × Γ₀, inferInstance,
    fun z => X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
      Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1,
    fun z => by rw [ecomp z, X.tr_q, X.tr_q], hgal, hspl, fun y => ?_⟩
  refine pull_base Θ _ _ _ (X.q m) (X.tr_q m i 1 a1 b1) (fun z => by rw [ecomp z, X.tr_q])
    (fun y => ?_) _ y
  have hHop := (hEx X Θ hΘ i (cntFn (X.K i) K' (X.K m) h) hIsFn).1
  have hop := hHop m hMK (fun g hg => by
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact UpperTheory.Gal.G3.Tower.admitted.mul (HarishChandraLabels c hc) (X.tower_admissible_self hk)) y
  have hsum := hSum Γ (X.K i) K' (X.K m) h hMK hKK hn hadm Γ₀ r hr huq (Θ.H (X.q m))
    (fun g => X.pl Θ m i g y) (fun k hk c hc => X.pl_left Θ (HarishChandraLabels c hc) hk y)
  refine ((by rw [X.pl_eq Θ (show X.admitted m i 1 from ⟨a1, b1⟩)] :
      Θ.pull (X.tr m i 1 a1 b1) (X.tr_q m i 1 a1 b1) (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y) =
        X.pl Θ m i 1 (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y))).trans
      (hop.trans (hsum.symm.trans (Finset.sum_congr rfl fun z _ => ?_)))
  beta_reduce
  rw [X.pl_eq Θ (adm z)]
  exact pull_congr' Θ (ecomp z).symm _ _ y

theorem UpperTheory.Gal.LocalSmoothExtension.memOp2_of :
    KNNormal → CntFn → CntSum → SigmaFEt → SigmaSplit → UpperTheory.Gal.G3.TwGal → UpperTheory.Gal.G3.HopEx.{0} → MemOp := by
  intro hKN hFn hSum hSig hSpl hGal hEx p _ D G L R _ _ gb k T N J g j
  have hMN : L.KN ↑(g j).M ≤ L.KN ↑N := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hMK' : L.KN ↑(g j).M ≤ (g j).K := hMN.trans (g j).le
  have hnorm := hKN p D G L ↑(g j).M
  have hpos : 0 < (↑(g j).M : ℕ) := by
    have := (g j).M.2.1
    omega
  have hidx : (L.KN ↑(g j).M).relIndex (g j).K ≠ 0 := by
    intro h0
    apply hnorm.2 hpos
    rw [← Subgroup.relIndex_mul_relIndex (hHK := hMK') (hKL := (g j).le_one), h0, zero_mul]
  have hΔ : ∀ c ∈ (g j).K, (g j).h * c ∈ T.X.Δ := fun c hc =>
    (T.Δ_eq _).2 (UpperTheory.Gal.Int.Geo.Integ.mul (g j).int
      (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc)))
  have a1 : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have b1 : ∀ u ∈ T.X.K (T.lev (g j).M), (1 : G.GAf) * u * 1⁻¹ ∈ T.X.K (T.lev N) := by
    intro u hu
    rw [T.K_eq] at hu ⊢
    simpa using hMN hu
  have aT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, (g j).h * (c.out : G.GAf) ∈ T.X.Δ :=
    fun c => hΔ _ c.out.2
  have bT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, ∀ u ∈ T.X.K (T.lev (g j).M),
      (g j).h * (c.out : G.GAf) * u * ((g j).h * (c.out : G.GAf))⁻¹ ∈ T.X.K (T.lev N) := by
    intro c u hu
    rw [T.K_eq] at hu ⊢
    exact (g j).adm _ c.out.2 u hu
  exact op_core hFn hSum hSig hSpl hGal hEx T.X (T.lev N) (T.lev (g j).M) (L.KN ↑N) (g j).K
    (L.KN ↑(g j).M) (g j).h (T.K_eq N) (T.K_eq _) hMN (g j).le
    (fun c hc u hu => hnorm.1 c ((g j).le_one hc) u hu) hidx (g j).adm hΔ a1 b1 aT bT
end

