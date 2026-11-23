module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.IneTriv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem res_one_lemma {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (y : A) (hy : IsLocalRing.residue B (f y) = 1) : IsLocalRing.residue A y = 1 := by
  change Ideal.Quotient.mk _ (f y) = Ideal.Quotient.mk _ 1 at hy
  change Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ 1
  rw [Ideal.Quotient.eq] at hy ⊢
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
  intro hu
  apply hy
  simpa using hu.map f

theorem UpperTheory.V.Ws.P1.ineTriv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q → ∀ u, ∀ g ∈ K.r.Ip u, ρ g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ u g hg
  simp only [W.Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg
  obtain ⟨hgu, hgc⟩ := hg
  unfold UpperTheory.V.W.HidaSetting.Lev.frame at hgu u
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hgu
  have hu : (u : W.Plc (W.Lp ↥T.L)) ∈ K.s.St := u.2
  have hsurj : ∀ b : Bool, ∀ j : Fin 4, ∃ i, lab b i = j := by decide
  have key : ∀ i, IsLocalRing.residue c'.O
      ((K.κ g' : c'.O) * inc h (D.ps (lab T.pr i) (resQ T.L g') : c.O)) = 1 := by
    intro i
    have e := K.chib i g'
    rw [hgc i, Units.val_one] at e
    exact e.symm
  have hκr : IsLocalRing.residue c'.O (K.κ g' : c'.O) = 1 := by
    obtain ⟨i, hi⟩ := hsurj T.pr 3
    have e := key i
    rw [hi] at e
    simpa [Raw.ps] using e
  have hres : ∀ j, IsLocalRing.residue c.O (D.ps j (resQ T.L g') : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj T.pr j
    have e := key i
    rw [hi, map_mul, hκr, one_mul] at e
    exact res_one_lemma (inc h) _ e
  have hrb : D.rbar (resQ T.L g') = 1 := by
    have hf : (fun i => IsLocalRing.residue c.O (D.ps i (resQ T.L g') : c.O)) = fun _ => 1 := funext hres
    show (RingHom.mapMatrix (IsLocalRing.residue c.O))
      (Matrix.diagonal fun i => (D.ps i (resQ T.L g') : c.O)) = 1
    rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), hf, Matrix.diagonal_one]
  have hnl : ¬ (K.s.A ↑u).valuation (l : Ω) < 1 := by
    intro hlt
    have hin := (K.s.hA ↑u (l : 𝓞 (W.Lp ↥T.L))).mp (by simpa using hlt)
    exact K.s.St_l ↑u hu (by simpa using hin)
  obtain ⟨m, hm, hκt⟩ := K.tame
  have hκm := hκt (K.s.A ↑u) hnl g' hg'
  have hκ1 : (K.κ g' : c'.O) = 1 :=
    (coefRes c').2.2.2 m _ hm (by rw [← Units.val_pow_eq_pow_val, hκm, Units.val_one]) hκr
  have hQr : Q.r (resLe T.F_le g') = 1 := by
    apply hQ.kill
    unfold UpperTheory.V.Ws.Tower.fr
    simp only [Set.mem_setOf_eq]
    refine ⟨K.s.A ↑u, ?_, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hp
      subst hp
      exact hnl
    · exact ((towerGal D T).2.2.2.2.2 _ g').2.mpr hg'
    · rw [((towerGal D T).2.2.2.2.1 g').1]
      exact hrb
  have e := hρ g'
  rw [hQr, hκ1, map_one, one_smul] at e
  exact Units.ext e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.MapsPt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_pt {A B R : Type} [CommRing A] [CommRing B] [CommRing R] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* R) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (y (i b) • M.map y).charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), (UpperTheory.V.Ws.P1.cpSmul _ _).1, ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.P1.mapsPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ →
          ∀ (R : Type) [CommRing R] [Algebra c'.O R] (y : X.A →ₐ[c'.O] R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ),
          K.IsRho ρ (X.P.map (y : X.A →+* R)) → K.IsPsi ψ (X.P.map (y : X.A →+* R)) →
          B.u.Maps (((y : X.A →+* R).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B)) (W.GDet.ofRep (W.mat ρ)) ψ := by
  intro Ω _ _ _ l _ c D T c' h K X B φ hφ R _ _ y ρ ψ hρ hψ
  have hs : ∀ a : c'.O, (y : X.A →+* R) (algebraMap X.B X.A (algebraMap c'.O X.B a)) = algebraMap c'.O R a := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    exact y.commutes a
  refine ⟨UpperTheory.V.Ws.P1.detExt _ _ _ fun g0 => ?_, fun v i => ?_⟩
  · obtain ⟨g, rfl⟩ := (UpperTheory.V.Ws.phiKer K.V).1 g0
    refine Eq.trans ?_ ((AlgebraTools.Det.repApi _).2.1 _).symm
    rw [← Polynomial.map_map]
    refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
    rw [scale_pt _ X.inj _ _ _ (X.cp_map _), hs, pow_zero, mul_one]
    exact congrArg Matrix.charpoly (hρ g).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    have hd0 : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) := by
      intro v g
      rw [← K.hA v]; exact g.2
    have hd := hd0 v g
    refine Eq.trans ?_ (hψ v i g).symm
    refine (congrArg (fun b => (y : X.A →+* R) (algebraMap X.B X.A b)) (hφ.2 v i g)).trans ?_
    simp only [pow_zero, mul_one]
    rw [map_mul, map_mul, hs, X.ψ_map _ _ _ hd]
    exact congrArg _ ((UpperTheory.V.Ws.sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* R) X.P).1 _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedDet
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.redDet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ρ : K.V.frame.G₀ →* GL (Fin 4) (PowerSeries k), K.IsRho ρ Q →
          (W.GDet.ofRep (W.mat ρ)).map (PowerSeries.constantCoeff : PowerSeries k →+* k) = K.r.Dbar.map (algebraMap (ResidueField c'.O) k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ρ hρ
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  rw [W.Resid.Dbar, (AlgebraTools.Det.repApi (W.diagRep K.r.chib)).2.2.2.2.2.1 (algebraMap (ResidueField c'.O) k)]
  apply P1.detExt
  intro g
  rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.1, (AlgebraTools.Det.repApi _).2.1]
  obtain ⟨g', hg'⟩ := (phiKer K.V).1 g
  subst hg'
  have hlc : ∀ M : Matrix (Fin 4) (Fin 4) (PowerSeries k),
      (PowerSeries.constantCoeff : PowerSeries k →+* k) M.charpoly.leadingCoeff ≠ 0 := by
    intro M
    rw [(Matrix.charpoly_monic M).leadingCoeff, map_one]
    exact one_ne_zero
  rw [hρ g', (P1.cpSmul _ _).1, map_scaleRoots _ _ _ (hlc _), hQ.cp,
    (P1.cpSmul _ (0 : Matrix (Fin 4) (Fin 4) k)).2]
  change _ = ((Matrix.diagonal fun i => ((K.r.chib i (K.V.pr g') : (ResidueField c'.O)ˣ) : ResidueField c'.O)).map
    (algebraMap (ResidueField c'.O) k)).charpoly
  rw [Matrix.diagonal_map (map_zero _), Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [K.chib i g', hc, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (↥c'.O) (ResidueField ↥c'.O) k, map_mul (algebraMap c'.O k)]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedPsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (φ : R →+* S) (hφ : I ≤ J.comap φ) {f : Γ → R} (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap φ := (Ideal.pow_right_mono hφ N).trans (Ideal.le_comap_pow φ N)
  exact (hf N).comp (Ideal.quotientMap (J ^ N) φ hN)

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  have h := IsLocallyConstant.comp₂ (hf N) (hg N) (· * ·)
  convert h using 1
  funext x
  simp [map_mul]

private theorem ac_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) : AdicCont I fun x => f (u x) :=
  fun N => (hf N).comp_continuous hu

theorem UpperTheory.V.Ws.P1.redPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* (PowerSeries k)ˣ, K.IsPsi ψ Q →
          (∀ v i, W.pushCh (PowerSeries.constantCoeff : PowerSeries k →+* k) (ψ v i) = W.pushCh (algebraMap (ResidueField c'.O) k) (K.r.psib v i)) ∧
          ∀ v i, AdicCont (maximalIdeal (PowerSeries k)) fun g => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ψ hψ
  obtain ⟨-, -, hcont, -, hres, hdec⟩ := P1.towerGal D T
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  constructor
  · intro v i
    ext g
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i g, map_mul, K.psib v i g, K.chib i]
    obtain ⟨g, hg0⟩ := (show ↥(Dec (K.s.A ↑(show W.Vl l T.L from v))) from g)
    have hg : (resLe T.F_le) g ∈ Dec (T.pl (K.e v)) := by
      rw [← K.hA v]
      exact (hdec _ _).1.2 hg0
    rw [hQ.psi _ _ _ hg, (hres g).1, hc, map_mul (residue _), map_mul,
      ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  · intro v i
    have hφ : maximalIdeal c'.O ≤ (maximalIdeal (PowerSeries k)).comap (algebraMap c'.O (PowerSeries k)) := by
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, hc, hQ.loc a ha]
      exact not_isUnit_zero
    have h1 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1)) :=
      ac_comp (ac_map _ hφ K.κ_cont) continuous_subtype_val
    have h2 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => Q.ψ (K.e v) i (resLe T.F_le g.1)) := by
      have := (sxAdicMat _ _ hQ.cont).2 (adj (Q.n (K.e v))) (Q.n (K.e v)) i i
      exact ac_comp this (hcont.comp continuous_subtype_val)
    have key := ac_mul h1 h2
    have e : (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k)) =
        fun g => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1) * Q.ψ (K.e v) i (resLe T.F_le g.1) :=
      funext fun g => hψ v i g
    show AdicCont _ (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k))
    rw [e]
    exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceOfCp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_of_cp {R k : Type} [CommRing R] [Field k] (f : R →+* k) (M : Matrix (Fin 4) (Fin 4) R) (a : Fin 4 → k)
    (h : M.charpoly.map f = ∏ i, (X - C (a i))) : f M.trace = ∑ i, a i := by
  have h1 := Matrix.trace_eq_neg_charpoly_nextCoeff (M.map f)
  rw [Matrix.charpoly_map, h, Polynomial.prod_X_sub_C_nextCoeff, neg_neg] at h1
  rw [← h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem UpperTheory.V.Ws.P1.irrL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (x : W.Point K.r) (Q : PD T.ι (G T.F Ω) x.A), T.PsPair h x.K Q → K.IsRho x.ρ Q → Irr (mapRep (algebraMap x.A x.Fr) Q.r) →
          U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) := by
  intro Ω _ _ _ l hl c D T c' h K x Q hP hρ hI
  obtain ⟨hrange, -, -, hidx, hres, -⟩ := UpperTheory.V.Ws.P1.towerGal D T
  have hsurj := (UpperTheory.V.Ws.phiKer K.V).1
  have htow : ∀ a : c'.O, algebraMap (ResidueField c'.O) x.K (residue c'.O a) = algebraMap c'.O x.K a :=
    fun a => (IsScalarTower.algebraMap_apply c'.O (ResidueField c'.O) x.K a).symm
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have h2 : (2 : x.Fr) ≠ 0 := by
    haveI := (UpperTheory.V.Ws.P1.coefRes c').2.1
    intro h0
    have h1 : (2 : x.A) = 0 := hinj (by rw [map_ofNat, map_zero]; exact h0)
    have h3 : (2 : x.K) = 0 := by
      have := congrArg (PowerSeries.constantCoeff : PowerSeries x.K →+* x.K) h1
      rwa [map_ofNat, map_zero] at this
    have h4 : ((2 : ℕ) : ResidueField c'.O) = 0 :=
      (algebraMap (ResidueField c'.O) x.K).injective (by rw [map_natCast, map_zero]; exact_mod_cast h3)
    exact K.s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h4))
  let χ : Fin (3 + 1) → G T.F Ω →* x.Kˣ := fun i =>
    W.pushCh ((algebraMap c'.O x.K).comp (inc h)) ((chi D T.pr i).comp (resQ T.F))
  have hχ : Function.Injective fun i => (χ i).comp T.GalL.subtype := by
    intro i j hij
    refine K.r.chib_inj (MonoidHom.ext fun y => ?_)
    obtain ⟨g, rfl⟩ := hsurj y
    have hg : resLe T.F_le g ∈ T.GalL := hrange ▸ ⟨g, rfl⟩
    have e : algebraMap c'.O x.K (inc h (chi D T.pr i (resQ T.L g))) =
        algebraMap c'.O x.K (inc h (chi D T.pr j (resQ T.L g))) := by
      have e1 := congrArg Units.val (DFunLike.congr_fun hij ⟨_, hg⟩)
      rw [← (hres g).1]
      exact e1
    apply Units.ext
    apply (algebraMap (ResidueField c'.O) x.K).injective
    rw [K.chib, K.chib, htow, htow, map_mul, map_mul, e]
  have htr : T.GalL = ⊤ ∨ ∃ g, g ∉ T.GalL ∧ (mapRep (algebraMap x.A x.Fr) Q.r g).trace ≠ 0 := by
    refine (UpperTheory.V.Ws.P1.trNe T.GalL χ hχ).imp id fun ⟨g, hg, hs⟩ => ⟨g, hg, fun h0 => hs ?_⟩
    have e1 : (Q.r g).trace = 0 := hinj (by
      rw [map_zero, ← h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum])
    have e2 := trace_of_cp _ _ _ (hP.cp g)
    rw [e1, map_zero] at e2
    exact e2.symm
  have hM := UpperTheory.V.Ws.P1.irrTr (algebraMap x.Fr x.Fb) T.GalL _ h2 hI hidx htr
  intro U hW
  refine hM U fun y hy v hv => ?_
  rw [← hrange] at hy
  obtain ⟨g, rfl⟩ := hy
  have h5 := hW (K.V.pr g) trivial v hv
  let u : x.Fbˣ := Units.map (((algebraMap x.Fr x.Fb).comp ((algebraMap x.A x.Fr).comp (algebraMap c'.O x.A)) : c'.O →+* x.Fb) : c'.O →* x.Fb) (K.κ g)
  have e : W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF) (K.V.pr g) =
      (u : x.Fb) • mapRep (algebraMap x.Fr x.Fb) (mapRep (algebraMap x.A x.Fr) Q.r) (resLe T.F_le g) := by
    ext i j
    have e0 := congrFun (congrFun (hρ g) i) j
    show algebraMap x.Fr x.Fb (algebraMap x.A x.Fr (W.mat x.ρ (K.V.pr g) i j)) = _
    rw [e0, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    rfl
  rw [e, Matrix.smul_mulVec] at h5
  exact (U.smul_mem_iff u.ne_zero).1 h5
end

