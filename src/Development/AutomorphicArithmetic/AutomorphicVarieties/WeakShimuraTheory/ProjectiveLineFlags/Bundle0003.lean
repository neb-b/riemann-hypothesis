module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.AcClosed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f)
    (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

private theorem ac_map {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [CommRing R] {J : Ideal O} {I : Ideal R} (φ : O →+* R)
    (h : ∀ a ∈ J, φ a ∈ I) {f : Γ → O} (hf : AdicCont J f) : AdicCont I fun x => φ (f x) := by
  intro N
  have hJ : Ideal.map φ J ≤ I := Ideal.map_le_iff_le_comap.mpr (fun a ha => h a ha)
  have hN : J ^ N ≤ Ideal.comap φ (I ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hJ N
  have := (hf N).comp (Ideal.Quotient.lift (J ^ N) ((Ideal.Quotient.mk (I ^ N)).comp φ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext x
  rfl

private theorem ac_closed {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} [IsHausdorff I R] {f : Γ → R}
    (hf : AdicCont I f) (y : R) : IsClosed {x | f x = y} := by
  have hset : {x | f x = y} =
      ⋂ N : ℕ, {x | Ideal.Quotient.mk (I ^ N) (f x) = Ideal.Quotient.mk (I ^ N) y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro hx N
      rw [hx]
    · intro hx
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro N
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using Ideal.Quotient.eq.mp (hx N)
  rw [hset]
  exact isClosed_iInter fun N => ((hf N).isClopen_fiber _).isClosed

theorem UpperTheory.V.Ws.P1.rhoEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (I : Ideal R) [IsHausdorff I R], (∀ a ∈ maximalIdeal c'.O, algebraMap c'.O R a ∈ I) → (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → Q.Cont I →
          ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) R, K.IsRho ρ Q ∧ ∀ a b, AdicCont I fun g => W.mat ρ g a b := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q I _ hI hpair hcont
  let σ : G T.L Ω →* M4 R :=
    { toFun := fun g => algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }
  let ρ' : G T.L Ω →* GL (Fin 4) R := σ.toHomUnits
  have hρ' : ∀ g, ((ρ' g : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g := fun g => rfl
  have hent : ∀ a b, AdicCont I fun g => σ g a b := by
    intro a b
    have h1 : AdicCont I fun g : G T.L Ω => algebraMap c'.O R (K.κ g : c'.O) :=
      ac_map (algebraMap c'.O R) hI K.κ_cont
    have h2 : AdicCont I fun g : G T.L Ω => Q.r (resLe T.F_le g) a b := by
      intro N
      exact (hcont a b N).comp_continuous (P1.towerGal D T).2.2.1
    exact ac_mul h1 h2
  have hker : K.V.pr.ker ≤ ρ'.ker := by
    apply (phiKer K.V).2.2 ρ'.ker
    · have hset : (ρ'.ker : Set (G T.L Ω)) =
          ⋂ a, ⋂ b, {g | σ g a b = (1 : Matrix (Fin 4) (Fin 4) R) a b} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
        rw [← Units.val_eq_one, hρ']
        exact ⟨fun hg a b => by rw [hg], fun hg => Matrix.ext hg⟩
      rw [hset]
      exact isClosed_iInter fun a => isClosed_iInter fun b => ac_closed (hent a b) _
    · intro A v hAv hv g hg
      rw [K.hV] at hv
      obtain ⟨hκ, hr⟩ := K.unr A v hAv hv g hg
      have hl : ¬ A.valuation (l : Ω) < 1 := by
        intro hlt
        apply hv
        left
        have hmem := (hAv (l : 𝓞 (W.Lp T.L))).mp (by simpa using hlt)
        simpa using hmem
      have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
        change ∃ A', Raw.Away (insert l ∅) A' ∧ resLe T.F_le g ∈ Ine A' ∧
          D.rbar ((resQ T.F) (resLe T.F_le g)) = 1
        refine ⟨A, ?_, ((P1.towerGal D T).2.2.2.2.2 A g).2.mpr hg, ?_⟩
        · intro p hp
          simp at hp
          subst hp
          exact hl
        · rw [((P1.towerGal D T).2.2.2.2.1 g).1]
          exact hr
      rw [MonoidHom.mem_ker, ← Units.val_eq_one, hρ']
      show algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g) = 1
      rw [hκ, hpair.kill _ hN]
      simp
  let e := QuotientGroup.quotientKerEquivOfSurjective K.V.pr (phiKer K.V).1
  let ρ : K.V.frame.G₀ →* GL (Fin 4) R :=
    (QuotientGroup.lift K.V.pr.ker ρ' hker).comp e.symm.toMonoidHom
  have hρ : ∀ g, ρ (K.V.pr g) = ρ' g := by
    intro g
    have he : e.symm (K.V.pr g) = (g : G T.L Ω ⧸ K.V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift K.V.pr.ker ρ' hker (e.symm (K.V.pr g)) = ρ' g
    rw [he]
    rfl
  have hmat : ∀ g, W.mat ρ (K.V.pr g) = σ g := by
    intro g
    show ((ρ (K.V.pr g) : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g
    rw [hρ, hρ']
  refine ⟨ρ, fun g => ?_, fun a b => ?_⟩
  · rw [hmat]
    rfl
  · intro N
    have hq := (phiKer K.V).2.1
    have heq : (fun x => Ideal.Quotient.mk (I ^ N) (W.mat ρ x a b)) ∘ K.V.pr =
        fun g => Ideal.Quotient.mk (I ^ N) (σ g a b) := by
      funext g
      show Ideal.Quotient.mk (I ^ N) (W.mat ρ (K.V.pr g) a b) = _
      rw [hmat]
    intro s
    have hopen := hent a b N s
    rw [← heq] at hopen
    exact hq.isOpen_preimage.mp hopen
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondA
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.condA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ), K.IsPsi ψ Q → (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, Q.ψ v i s ≠ Q.ψ v j s) →
          Nonempty K.V.frame.Vl ∧ ∀ v i j, i ≠ j → ∃ g, K.V.frame.φ v g ∈ K.V.frame.G' ∧ K.r.psib v i g = K.r.psib v j g ∧ ψ v i g ≠ ψ v j g := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K R _ _ Q ψ hψ hsep
  obtain ⟨hrange, -, -, -, hres, hloc⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hlev := P1.levEps K.V
  refine ⟨hlev.2.2.1, fun v i j hij => ?_⟩
  obtain ⟨s, ⟨hsI, hscyc, hsr⟩, hne⟩ := hsep (K.e v) i j hij
  have hsL : s ∈ T.GalL := hfit.1.unr _ hsI
  rw [← hrange] at hsL
  obtain ⟨g', rfl⟩ := hsL
  have hgD : g' ∈ (Dec (K.s.A (show W.Vl l T.L from v).1) : Subgroup (G T.L Ω)) := by
    rw [K.hA v]
    exact Ine_le_Dec _ (((hloc _ g').2).1 hsI)
  have hr : D.rbar (resQ T.L g') = 1 := by rw [← (hres g').1]; exact hsr
  have hk : ∀ k, residue c'.O (inc h ↑(chi D T.pr k (resQ T.L g'))) = 1 := by
    intro k
    have e := congrArg (fun M => M (lab T.pr k) (lab T.pr k)) hr
    simp [Raw.rbar, Raw.r0, mapRep, diagRep] at e
    rw [← ResidueField.map_residue]
    simp [chi, e]
  refine ⟨⟨g', hgD⟩, ?_, ?_, ?_⟩
  · show K.V.pr g' ∈ K.V.frame.G'
    rw [(hlev.2.1 g'), ← (hres g').2.1]
    exact hscyc
  · have hc : K.r.chib i (K.V.pr g') = K.r.chib j (K.V.pr g') := by
      apply Units.ext
      rw [K.chib, K.chib, map_mul, map_mul, hk, hk]
    exact (K.psib v i ⟨g', hgD⟩).trans (hc.trans (K.psib v j ⟨g', hgD⟩).symm)
  · intro heq
    apply hne
    have e1 := hψ v i ⟨g', hgD⟩
    have e2 := hψ v j ⟨g', hgD⟩
    rw [heq] at e1
    have hu : IsUnit (algebraMap c'.O R ↑(K.κ g')) := (K.κ g').isUnit.map _
    exact hu.mul_left_cancel (e1.symm.trans e2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondC
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Ws.P1.condC :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (η : K.V.frame.G₀ →* (ResidueField c'.O)ˣ), η ^ 2 = 1 → (K.V.frame.eps c'.O (ResidueField c'.O)).ker ≤ η.ker →
          (∀ i, ∃ j, η * K.r.chib i = K.r.chib j) → η = 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K η hη2 hker hperm
  obtain ⟨hrange, hinj, -, -, hres, -⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hgood : D.Good := by
    rcases hfit.2 with ⟨h2, -⟩ | ⟨h3, -⟩
    exacts [h2.1, h3.1]
  have hlev := P1.levEps K.V
  have hsurj := (phiKer K.V).1
  have hφ : Function.Injective (ResidueField.map (inc h)) := (ResidueField.map (inc h)).injective
  have hη2' : η * η = 1 := by rw [← pow_two]; exact hη2
  have hE2 : ∀ x, ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) * η (K.V.pr x) = 1 := fun x =>
    congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hη2'
  have hpm : ∀ x, ∃ y : ResidueField c.O, ResidueField.map (inc h) y = η (K.V.pr x) := by
    intro x
    rcases mul_self_eq_one_iff.mp (hE2 x) with e | e
    · exact ⟨1, by rw [map_one, e]⟩
    · exact ⟨-1, by rw [map_neg, map_one, e]⟩
  choose f hf using hpm
  have hff : ∀ x, f x * f x = 1 := fun x => hφ (by rw [map_mul, hf, map_one, hE2])
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    hφ (by rw [map_mul, hf, hf, hf]; exact congrArg Units.val ((η.comp K.V.pr).map_mul a b))
  have hf1 : f 1 = 1 := hφ (by rw [hf, map_one]; exact congrArg Units.val (η.comp K.V.pr).map_one)
  let F' : G T.L Ω →* (ResidueField c.O)ˣ :=
    { toFun := fun x => ⟨f x, f x, hff x, hff x⟩
      map_one' := Units.ext hf1
      map_mul' := fun a b => Units.ext (hfmul a b) }
  let e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let η' : T.GalL →* (ResidueField c.O)ˣ := F'.comp e.symm.toMonoidHom
  have hxg : ∀ g : T.GalL, resLe (Tower.F_le T) (e.symm g) = (g : G T.F Ω) := fun g =>
    congrArg Subtype.val (e.apply_symm_apply g)
  have hmain : η' = 1 := by
    refine hfit.1.g3' η' ?_ ?_ ?_
    · rw [pow_two]
      refine MonoidHom.ext fun g => ?_
      exact Units.ext (hff _)
    · intro g hom
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      rw [hq] at hom
      have hb := hgood.om_bar (resQ T.L (e.symm g))
      simp only [Raw.bar, hom, Units.val_one, map_one] at hb
      have heps : K.V.frame.eps c'.O (ResidueField c'.O) (K.V.pr (e.symm g)) = 1 := by
        apply Units.ext
        rw [hlev.2.2.2 c'.O (ResidueField c'.O) (e.symm g), Units.val_one]
        have hc : (cycZ (↥T.L) Ω l) (e.symm g) = cycZ ℚ Ω l (resQ T.L (e.symm g)) := ((hres _).2.2).symm
        have key : algebraMap ℤ_[l] c'.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g))) =
            inc h (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) :=
          ((Subalgebra.inclusion h).commutes _).symm
        show residue c'.O (algebraMap ℤ_[l] c'.O ↑(cycZ (↥T.L) Ω l (e.symm g))) = 1
        rw [hc, key, ← ResidueField.map_residue]
        have hb' : residue c.O (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) = 1 := by
          first | exact hb | exact hb.symm
        rw [hb', map_one]
      have hη1 : η (K.V.pr (e.symm g)) = 1 := hker heps
      apply Units.ext
      show f (e.symm g) = 1
      exact hφ (by rw [hf, hη1]; simp)
    · intro i
      obtain ⟨j, hj⟩ := hperm i
      refine ⟨j, fun g => ?_⟩
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      show f (e.symm g) * residue c.O ↑(chi D T.pr i (resQ T.F ↑g)) = residue c.O ↑(chi D T.pr j (resQ T.F ↑g))
      rw [hq]
      generalize e.symm g = x
      have hc' : ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) *
          (K.r.chib i (K.V.pr x) : ResidueField c'.O) = K.r.chib j (K.V.pr x) :=
        congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hj
      rw [K.chib i x, K.chib j x, map_mul (residue c'.O), map_mul (residue c'.O)] at hc'
      have hκ : residue c'.O (K.κ x : c'.O) ≠ 0 := ((K.κ x).isUnit.map (residue _)).ne_zero
      apply hφ
      rw [map_mul, ResidueField.map_residue (inc h), ResidueField.map_residue (inc h), hf x]
      apply mul_left_cancel₀ hκ
      linear_combination hc'
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have h1 : f x = 1 := by
    have hm := congrArg (fun θ => ((θ (e x) : (ResidueField c.O)ˣ) : ResidueField c.O)) hmain
    rw [show f x = f (e.symm (e x)) by rw [e.symm_apply_apply]]
    exact hm
  apply Units.ext
  rw [← hf x, h1, map_one]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondDRoots
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.P1.condD_roots : ∀ w ∈ roots, ∃ i j : Fin 4, w = wt i j := by
  decide

private theorem UpperTheory.V.Ws.P1.condD_rt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g) (Φ.χ 3 g), mul_inv_cancel_right]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)

theorem UpperTheory.V.Ws.P1.condD :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h), ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (K.r.chib i / K.r.chib j) ^ n ≠ 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K
  obtain ⟨w, hw, hord⟩ := hfit.1.ord
  obtain ⟨i, j, rfl⟩ := condD_roots w hw
  refine ⟨i, j, fun n hn hn4 heq => ?_⟩
  obtain ⟨g, hgL, hne⟩ := hord n hn hn4
  obtain ⟨hrange, -, -, -, hres, -⟩ := P1.towerGal D T
  rw [← hrange] at hgL
  obtain ⟨g', hg'⟩ := hgL
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hΦ : (T.fr ∅).χ 0 g * (T.fr ∅).χ 3 g = (T.fr ∅).χ 1 g * (T.fr ∅).χ 2 g := by
    simp only [Tower.fr, chi, lab]
    cases T.pr <;> simp [Raw.ps, Raw.th, mul_comm]
  have hrt := condD_rt (T.fr ∅) g hΦ i j
  have hq : resQ T.F g = resQ T.L g' := by rw [← hg']; exact (hres g').1
  have hA : (T.fr ∅).χ i g = chi D T.pr i (resQ T.L g') := by rw [← hq]; rfl
  have hB : (T.fr ∅).χ j g = chi D T.pr j (resQ T.L g') := by rw [← hq]; rfl
  rw [hA, hB] at hrt
  have hAval : ((chi D T.pr i (resQ T.L g') : (c.O)ˣ) : c.O) =
      (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O) * (chi D T.pr j (resQ T.L g') : c.O) := by
    rw [← hrt, Units.val_mul]
  have hx : (K.r.chib i (K.V.pr g') / K.r.chib j (K.V.pr g')) ^ n = 1 :=
    DFunLike.congr_fun heq (K.V.pr g')
  have hx' := congrArg (fun u : (ResidueField c'.O)ˣ => (u : ResidueField c'.O)) hx
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one] at hx'
  rw [K.chib i g', K.chib j g', hAval] at hx'
  have hκ : residue c'.O (K.κ g' : c'.O) ≠ 0 := ((K.κ g').isUnit.map (residue _)).ne_zero
  have hBn : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue _)).ne_zero
  simp only [map_mul] at hx'
  rw [mul_div_mul_left _ _ hκ, mul_div_cancel_right₀ _ hBn] at hx'
  apply hne
  show (residue c.O (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O)) ^ n = 1
  apply (ResidueField.map (inc h)).injective
  rw [map_pow, map_one, ResidueField.map_residue]
  exact hx'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.FormEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem transpose_form_mul_involution {R : Type} [CommRing R] (J C : M4 R) (hJ : J.transpose = -J) (hC : C * C = 1)
    (h : C.transpose * J * C = -J) : (J * C).transpose = J * C := by
  have hT : C.transpose * J = -(J * C) := by
    calc C.transpose * J = C.transpose * J * (C * C) := by rw [hC, Matrix.mul_one]
      _ = -J * C := by rw [← Matrix.mul_assoc, h]
      _ = -(J * C) := Matrix.neg_mul _ _
  rw [Matrix.transpose_mul, hJ, Matrix.mul_neg, hT, neg_neg]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {R : Type} [CommRing R] (J C A : M4 R) (hC : C * C = 1) (x y ν : R)
    (h : A.transpose * J * A = ν • J) :
    (x • A).transpose * (J * C) * (y • (C * A * C)) = (x * y * ν) • (J * C) := by
  have hA : A.transpose * (J * C) * (C * A * C) = ν • (J * C) := by
    calc A.transpose * (J * C) * (C * A * C) = A.transpose * J * (C * C) * A * C := by
          simp only [Matrix.mul_assoc]
      _ = (ν • J) * C := by rw [hC, Matrix.mul_one, h]
      _ = ν • (J * C) := Matrix.smul_mul _ _ _
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA, smul_smul, smul_smul]
  congr 1
  ring

private theorem unit_aux {R : Type} [CommRing R] (e : Rˣ) (z : R) (h : z * (e : R) ^ 3 = 1) :
    ((e ^ (1 - ((4 : ℕ) : ℤ)) : Rˣ) : R) = z := by
  have h3 : ((1 : ℤ) - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [h3, zpow_neg, zpow_ofNat]
  rw [eq_comm]
  exact Units.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h)

private theorem exists_gl4_form_mul_involution {R : Type} [CommRing R] (J : (M4 R)ˣ) (C : M4 R) (hC : C * C = 1) :
    ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R) = (J : M4 R) * C := by
  exact ⟨J * ⟨C, C, hC, hC⟩, rfl⟩

theorem UpperTheory.V.Ws.P1.formEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ P : GL (Fin 4) R, (P : Matrix (Fin 4) (Fin 4) R).transpose = P ∧ K.V.frame.IsForm c'.O 4 ρ P := by
  intro Ω _ _ _ l _ c D T hF hD c' h K R _ _ Q ρ hQ hρ
  obtain ⟨J, hJ, hG⟩ := P1.gspForm R
  obtain ⟨cF, hc, hcc⟩ := P1.ccEx D T K.s
  obtain ⟨h2, hν⟩ := (X1.thFacts D T hF hD).2.2.1 cF hc
  obtain ⟨e1, -, -, e4⟩ := P1.levEps K.V
  have hC : Q.r cF * Q.r cF = 1 := by rw [← map_mul, h2, map_one]
  have hCJ : (Q.r cF).transpose * (J : M4 R) * Q.r cF = -(J : M4 R) := by
    rw [hG _ _ (hQ.mult cF), hν]
    simp
  obtain ⟨P, hP⟩ := exists_gl4_form_mul_involution J _ hC
  refine ⟨P, by rw [hP]; exact transpose_form_mul_involution _ _ hJ hC hCJ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := (phiKer K.V).1 x
  obtain ⟨g', hg, hg'⟩ := hcc g
  have hk := congrArg (algebraMap c'.O R) (K.conj g g' hg).1
  have h3 : Q.r (resLe T.F_le g') = Q.r cF * Q.r (resLe T.F_le g) * Q.r cF := by
    rw [hg', inv_eq_of_mul_eq_one_right h2, map_mul, map_mul]
  have h4 := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero _ _ _ hC (algebraMap c'.O R (K.κ g)) (algebraMap c'.O R (K.κ g')) _
    (hG _ _ (hQ.mult (resLe T.F_le g)))
  rw [map_mul, map_mul, map_mul, map_pow, map_one, ← e4 c'.O R g] at hk
  rw [e1 g g' hg, hρ g, hρ g', h3, unit_aux _ _ hk, hP]
  exact h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.HasFlagPush
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem up_diag_mul {R : Type} [CommRing R] {A B : M4 R} (hA : IsUp A) (hB : IsUp B) (i : Fin 4) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA i j h, zero_mul]
  · rw [hB j i h, mul_zero]

private theorem low_left {R : Type} [CommRing R] {N : M4 R} (h : IsLow N) : adj N * N = 1 := by
  have := h.1
  rwa [IsGSp, one_smul] at this

private theorem pair_psi_one {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Q.ψ v i 1 = 1 := by
  rw [PD.ψ, map_one, mul_one, low_left (hQ.low v), Matrix.one_apply_eq]

private theorem pair_psi_mul {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) {s t : Γ} (hs : s ∈ Φ.Gv v) (ht : t ∈ Φ.Gv v) :
    Q.ψ v i (s * t) = Q.ψ v i s * Q.ψ v i t := by
  rw [PD.ψ, PD.ψ, PD.ψ, ← up_diag_mul (hQ.flag v s hs) (hQ.flag v t ht), map_mul]
  have h1 : Q.n v * adj (Q.n v) = 1 := mul_eq_one_comm.1 (low_left (hQ.low v))
  have h2 : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
      adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by
    simp only [mul_assoc]
  rw [h2, h1, mul_one, mul_assoc (adj (Q.n v)) (Q.r s)]

private theorem hasFlag_push {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    {r : H →* GL (Fin n) A} {κ : Fin n → H →* Aˣ} (h : W.HasFlag r κ) :
    W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Matrix.GeneralLinearGroup.map f g, fun s => ?_⟩
  have key : ∀ i j, (Matrix.GeneralLinearGroup.map f g * W.pushRep f r s * (Matrix.GeneralLinearGroup.map f g)⁻¹ :
      GL (Fin n) B) i j = f ((g * r s * g⁻¹ : GL (Fin n) A) i j) := by
    intro i j
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (hg s).1 i j hij, map_zero]
  · rw [key, (hg s).2 i]
    rfl

theorem UpperTheory.V.Ws.P1.psiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ, K.IsPsi ψ Q ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (v : K.V.frame.Vl),
            W.HasFlag (W.pushRep f (ρ.comp (K.V.frame.φ v))) fun i => W.pushCh f (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ
  have hd : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    have h1 : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := by
      rw [← K.hA]; exact g.2
    exact h1
  let p : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* R := fun v i =>
    { toFun := fun g => algebraMap c'.O R (K.κ g) * Q.ψ (K.e v) i (resLe T.F_le g)
      map_one' := by
        rw [OneMemClass.coe_one, map_one, map_one, Units.val_one, map_one, one_mul]
        exact pair_psi_one (Φ := T.fr ∅) hQ (K.e v) i
      map_mul' := fun g g' => by
        have h2 := pair_psi_mul (Φ := T.fr ∅) hQ (K.e v) i (hd v g) (hd v g')
        rw [Subgroup.coe_mul, map_mul, map_mul, Units.val_mul, map_mul]
        erw [h2]
        exact mul_mul_mul_comm _ _ _ _ }
  refine ⟨fun v i => (p v i).toHomUnits, fun v i g => rfl, fun R' _ f v => hasFlag_push f ?_⟩
  have h1 : adj (Q.n (K.e v)) * Q.n (K.e v) = 1 := low_left (hQ.low (K.e v))
  refine ⟨⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩, fun s => ?_⟩
  have key : ∀ i j, ((⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R) *
      (ρ.comp (K.V.frame.φ v)) s *
      (⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R)⁻¹ : GL (Fin 4) R) i j =
      algebraMap c'.O R (K.κ s.1) *
        (adj (Q.n (K.e v)) * Q.r (resLe T.F_le s.1) * Q.n (K.e v)) i j := by
    intro i j
    change (adj (Q.n (K.e v)) * W.mat ρ (K.V.pr s.1) * Q.n (K.e v)) i j = _
    rw [hρ, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    have := hQ.flag (K.e v) _ (hd v s) i j hij
    erw [this]
    exact mul_zero _
  · rw [key]
    rfl
end

