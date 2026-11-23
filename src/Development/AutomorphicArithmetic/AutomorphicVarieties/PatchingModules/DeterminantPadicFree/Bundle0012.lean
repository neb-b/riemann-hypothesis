module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadic
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpl : p = l := by
    by_contra hne
    have hcop : l.Coprime p := (Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)
    have hu : IsUnit ((p : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
    have hu' := hu.map f
    rw [map_natCast, hpK] at hu'
    exact not_isUnit_zero hu'
  subst hpl
  exact hp

theorem UpperTheory.V.Pa.Det.kapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), PhiCond F.Γ l → Nonempty (Kap x) := by
  intro l _ F n x hΦ
  letI : Field x.K := x.field
  haveI : Finite x.K := x.fin
  letI : Algebra ℤ_[l] x.K := x.algZ
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  have hΦ0 : PhiCond F.G₀ l := UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ
  have hρ : x.ρX x.A = fun g => mat x.ρ g := by
    funext g
    simp [UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]
  obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A)
    (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have hSfg : S.FG := by
    refine UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0
      ?_ ?_ ?_
    · intro N
      simp only [MonoidHom.one_apply]
      exact IsLocallyConstant.const (X := F.G₀) _
    · intro i j
      have h := x.cont i j
      simpa [PowerSeries.maximalIdeal_eq_span_X] using h
    · intro z hz
      rw [← SetLike.mem_coe, hS] at hz
      refine ⟨hz.2.1, ?_⟩
      intro g _ h _
      have e := hz.2.2.1 g h
      rw [hρ] at e
      simpa using e
  obtain ⟨g, κ, hmem, hind, hgen⟩ :=
    UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg
  have hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro j
    rw [← hS]
    exact hmem j
  have hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a,
      LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y :=
    fun j v => (hsel j).2.2.2.2.2 v
  choose Y hYmem hYloc using hloc
  refine ⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩
  · intro c hc
    apply hind c
    rw [← SetLike.mem_coe, hB]
    exact hc
  · intro z hz
    rw [← hS] at hz
    obtain ⟨s, c, hsc⟩ := hgen z hz
    refine ⟨s, c, ?_⟩
    rw [← hB]
    exact hsc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetFin
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ac_mul {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g * h g := by
  intro N
  simpa only [map_mul] using (hf N).comp₂ (hh N) (· * ·)

private theorem ac_add {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g + h g := by
  intro N
  simpa only [map_add (f := _)] using (hf N).comp₂ (hh N) (· + ·)

private theorem ac_const {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (c : R) :
    AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

private theorem ac_sum {G R ι : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (s : Finset ι)
    {f : ι → G → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (G := G) (I := I) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ac_add (hf a) ih

private theorem ac_map {G A R : Type} [TopologicalSpace G] [CommRing A] [CommRing R] (φ : A →+* R) (t : A)
    {f : G → A} (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {φ t}) fun g => φ (f g) := by
  intro N
  have hle : (Ideal.span {t}) ^ N ≤ ((Ideal.span {φ t}) ^ N).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  have h := (hf N).comp (Ideal.quotientMap ((Ideal.span {φ t}) ^ N) φ hle)
  simpa [Function.comp_def, Ideal.quotientMap_mk] using h

private theorem dd_sum {X ι Y : Type} [CommRing X] [AddCommMonoid Y] {g : ℕ} (p : DD X g → Y) (h0 : p 0 = 0)
    (ha : ∀ x y, p (x + y) = p x + p y) (s : Finset ι) (f : ι → DD X g) : p (∑ i ∈ s, f i) = ∑ i ∈ s, p (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using h0
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ha, ih]

private theorem epM_entry {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) := by
  have hm : ∀ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD X g)
      = (⟨0, Pi.single j (Z j a b), 0, 0⟩ : DD X g) := by
    intro j
    apply DD.ext
    · show Z j a b * 0 = 0
      simp
    · funext i
      show Z j a b * (Pi.single j (1 : X) : Fin g → X) i + (0 : Fin g → X) i * 0
        = (Pi.single j (Z j a b) : Fin g → X) i
      by_cases h : i = j
      · subst h
        simp
      · simp [Pi.single_apply, h]
    · funext i
      show Z j a b * (0 : Fin g → X) i + (0 : Fin g → X) i * 0 = (0 : Fin g → X) i
      simp
    · show Z j a b * 0 + 0 * 0 + ∑ k, ((0 : Fin g → X) k * (0 : Fin g → X) k
          + (0 : Fin g → X) k * (Pi.single j (1 : X) : Fin g → X) k) = 0
      simp
  simp_rw [hm]
  ext i
  · rw [dd_sum (fun x : DD X g => x.a) rfl (fun _ _ => rfl)]
    simp [DD.epM]
  · rw [dd_sum (fun x : DD X g => x.ep i) rfl (fun _ _ => rfl)]
    simp [DD.epM, Pi.single_apply]
  · rw [dd_sum (fun x : DD X g => x.ep' i) rfl (fun _ _ => rfl)]
    simp [DD.epM]
  · rw [dd_sum (fun x : DD X g => x.eta) rfl (fun _ _ => rfl)]
    simp [DD.epM]

private noncomputable def ddLin (A : Type) [CommRing A] (g : ℕ) :
    DD A g ≃ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
  { DD.equiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun c x => by
      have hc : c • x = DD.C c * x := rfl
      rw [hc]
      ext <;> simp [DD.equiv] }

private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  have hl : (algebraMap ℤ_[l] K) (l : ℤ_[l]) = 0 := by
    by_contra hne
    have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra ha0
      have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
        intro h
        apply ha0
        have hmem : a ∈ RingHom.ker (algebraMap ℤ_[l] K) := ha
        rw [h] at hmem
        exact hmem
      obtain ⟨m, hm⟩ := PadicInt.ideal_eq_span_pow_p hker
      have hmem : (l : ℤ_[l]) ^ m ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
        rw [hm]
        exact Ideal.subset_span rfl
      rw [RingHom.mem_ker, map_pow] at hmem
      exact hne (pow_eq_zero_iff'.mp hmem).1
    have : Finite ℤ_[l] := Finite.of_injective _ hinj
    have : Finite ℤ := Finite.of_injective (Int.cast : ℤ → ℤ_[l]) Int.cast_injective
    exact not_finite ℤ
  have hK : ((l : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] K)]
    exact hl
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr hK

private theorem lc_zp {l : ℕ} [Fact l.Prime] {G R : Type} [TopologicalSpace G] [CommRing R] (φ : ℤ_[l] →+* R)
    (hl : (l : R) = 0) {e : G → ℤ_[l]} (he : Continuous e) : IsLocallyConstant fun g => φ (e g) := by
  have hφ : IsLocallyConstant (φ : ℤ_[l] → R) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    rw [Metric.mem_ball, dist_eq_norm, PadicInt.norm_lt_one_iff_dvd] at hy
    obtain ⟨c, hc⟩ := hy
    have hy' : y = x + (l : ℤ_[l]) * c := by rw [← hc]; ring
    rw [hy', map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]
  exact hφ.comp_continuous he

theorem UpperTheory.V.Pa.Det.detFin :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (S : Set F.G₀), PhiCond F.Γ l → Detects k S → ∃ T : Finset F.G₀, (T : Set F.G₀) ⊆ S ∧ Detects k (T : Set F.G₀) := by
  intro l _ F n x k S hΦ hdet
  classical
  haveI : CharP x.K l := charK l x.K
  haveI : Module.Free x.A (DD x.A k.g) := Module.Free.of_equiv (ddLin x.A k.g).symm
  haveI : Module.Finite x.A (DD x.A k.g) := Module.Finite.equiv (ddLin x.A k.g).symm
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  let I : Ideal (DD x.A k.g) := Ideal.span {algebraMap x.A (DD x.A k.g) x.t}
  let χ : F.G₀ →* DD x.A k.g :=
    (algebraMap x.A (DD x.A k.g)).toMonoidHom.comp ((algebraMap ℤ_[l] x.A).toMonoidHom.comp
      ((Units.coeHom ℤ_[l]).comp (F.ε.comp F.η.ker.subtype)))
  let r : F.G₀ →* Matrix (Fin n) (Fin n) (DD x.A k.g) :=
    ⟨⟨k.ρ1 x.A, (Det.rho1Hom k x.A).1⟩, (Det.rho1Hom k x.A).2.1⟩
  let Zb : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {z | (∀ i j, AdicCont I fun g => z g i j) ∧ TwCoc (⇑χ) (⇑r) Set.univ z}
      zero_mem' := by
        refine ⟨fun _ _ => ac_const 0, fun g _ h _ => ?_⟩
        simp
      add_mem' := by
        intro a b ha hb
        refine ⟨fun i j => ac_add (ha.1 i j) (hb.1 i j), fun g _ h _ => ?_⟩
        simp only [Pi.add_apply]
        rw [ha.2 g trivial h trivial, hb.2 g trivial h trivial]
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
        abel
      smul_mem' := by
        intro c z hz
        refine ⟨fun i j => ?_, fun g _ h _ => ?_⟩
        · have h := ac_mul (ac_const (G := F.G₀) (I := I) (algebraMap x.A (DD x.A k.g) c)) (hz.1 i j)
          simpa [Algebra.smul_def] using h
        · simp only [Pi.smul_apply]
          rw [hz.2 g trivial h trivial, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm c (χ g)] }
  have hG : PhiCond F.G₀ l := Det.phiSub l F.η.ker F.η_open hΦ
  have he : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
  have hA : AdicCont (Ideal.span {x.t}) fun g : F.G₀ => algebraMap ℤ_[l] x.A (F.ε g) := by
    intro N
    have hl : ((l : ℕ) : x.A ⧸ (Ideal.span {x.t}) ^ N) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_natCast (algebraMap x.K x.A),
        CharP.cast_eq_zero, map_zero, map_zero]
    exact lc_zp ((Ideal.Quotient.mk _).comp (algebraMap ℤ_[l] x.A)) hl he
  have hχ : AdicCont I χ := ac_map (algebraMap x.A (DD x.A k.g)) x.t hA
  have hE : ∀ a b, AdicCont I fun g => DD.epM (fun j => (k.κ j g).map (algebraMap x.A x.A)) a b := by
    intro a b
    simp_rw [epM_entry]
    refine ac_sum _ (fun j => ac_mul ?_ (ac_const _))
    exact ac_map (algebraMap x.A (DD x.A k.g)) x.t ((k.mem j).2.1 a b)
  have hρ : ∀ a b, AdicCont I fun g => x.ρX (DD x.A k.g) g a b := by
    intro a b
    have h := x.cont a b
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_map (algebraMap x.A (DD x.A k.g)) PowerSeries.X h
  have hr : ∀ i j, AdicCont I fun g => r g i j := by
    intro i j
    show AdicCont I fun g => ((1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A))
      * x.ρX (DD x.A k.g) g) i j
    simp only [Matrix.mul_apply, Matrix.add_apply]
    exact ac_sum _ fun m => ac_mul (ac_add (ac_const _) (hE i m)) (hρ m j)
  have hFG : Zb.FG := Det.matFg l χ r Zb hG hχ hr (fun z hz => hz)
  let etaL : DD x.A k.g →ₗ[x.A] x.A :=
    (LinearMap.snd x.A _ _).comp ((LinearMap.snd x.A _ _).comp
      ((LinearMap.snd x.A _ _).comp (ddLin x.A k.g).toLinearMap))
  let f : S → (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) →ₗ[x.A] x.A := fun σ =>
    etaL.comp ((Matrix.traceLinearMap (Fin n) x.A (DD x.A k.g)).comp
      ((LinearMap.mulRight x.A (k.ρ1 x.A σ)).comp (LinearMap.proj (σ : F.G₀))))
  let B : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) := ⨅ σ : S, LinearMap.ker (f σ)
  obtain ⟨T, hT⟩ := Det.finSub x.t Zb B f PowerSeries.X_irreducible hFG
    (fun i b hb => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hb i))
    (fun z _ hz => ⟨0, by
      rw [pow_zero, one_smul]
      exact (Submodule.mem_iInf _).mpr fun i => LinearMap.mem_ker.mpr (hz i)⟩)
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro σ hσ
    rw [Finset.coe_map, Set.mem_image] at hσ
    obtain ⟨i, _, rfl⟩ := hσ
    exact i.2
  · intro z hz hvan
    have hzZ : z ∈ Zb := ⟨hz.2.1, fun g _ h _ => hz.2.2.1 g h⟩
    obtain ⟨s, hs⟩ := hT z hzZ (fun i hi => hvan _ (Finset.mem_map_of_mem _ hi))
    apply hdet z hz
    intro σ hσ
    have h1 : f ⟨σ, hσ⟩ (x.t ^ s • z) = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hs ⟨σ, hσ⟩)
    rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DiscStIff
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices
open UpperTheory.V.CA

private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  obtain ⟨-, -, hm, -⟩ := UpperTheory.V.CA.d_gmap D
  have e1 := (hm f (MonoidAlgebra.single g 1)).2 1
  have hs : (MonoidAlgebra.mapRingHom G f) (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    simp [MonoidAlgebra.mapRingHom]
  rw [hs, h] at e1
  have e2 : (GDet.ofRep ρ).tr (MonoidAlgebra.single g 1) = (ρ g).trace := by
    rw [← (UpperTheory.V.CA.d_toDet (GDet.ofRep ρ) _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
      ((UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 (by simpa using hn))]
    simp [GDet.repAlg]
  unfold GDet.tr at e2
  unfold GDet.tr
  rw [← e1, e2]

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Matrix.vecMul c (Matrix.of fun a b => (x a * y b).trace) = 0 := by
      funext b
      have h0 : ((∑ a, c a • x a) * y b).trace = 0 := by rw [hc]; simp
      rw [Finset.sum_mul, Matrix.trace_sum] at h0
      simpa [Matrix.vecMul, dotProduct, Matrix.trace_smul, smul_mul_assoc] using h0
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro i
    simp [this]
  by_cases hn : n = 0
  · subst hn
    exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin (n * n)) := ⟨⟨0, Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)⟩⟩
    have htop := hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K]
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : IsEmpty (Fin (0 * 0)) := ⟨fun i => Fin.elim0 i⟩
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      refine ⟨fun _ => 1, fun _ => 1, ?_⟩
      rw [Matrix.det_isEmpty, ← hQ, map_one]
      exact one_ne_zero
  · have key : ∀ g h' : Fin (n * n) → G,
        (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det ∉ Q ↔
          (Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace).det ≠ 0 := by
      intro g h'
      have hm : f.mapMatrix (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)) =
          Matrix.of fun i j => (ρ (g i) * ρ (h' j)).trace := by
        ext i j
        simp [tr_of_map hn D f ρ h, map_mul]
      have e := hQ (Matrix.of fun i j => D.tr (MonoidAlgebra.single (g i * h' j) 1)).det
      rw [RingHom.map_det, hm] at e
      exact not_congr e.symm
    unfold DiscSt
    constructor
    · rintro ⟨g, h', hd⟩
      rw [key] at hd
      exact span_of_gram _ (fun a => ρ (g a)) (fun b => ρ (h' b)) (fun a => ⟨g a, rfl⟩) hd
    · intro hs
      obtain ⟨x, hx, hd⟩ := (UpperTheory.V.CA.g_gram K (Fin n) _).1 hs
      choose gg hgg using hx
      refine ⟨fun i => gg (finProdFinEquiv.symm i), fun i => gg (finProdFinEquiv.symm i), ?_⟩
      rw [key]
      have hr : (Matrix.of fun i j => (ρ (gg (finProdFinEquiv.symm i)) * ρ (gg (finProdFinEquiv.symm j))).trace) =
          Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.of fun a b => (x a * x b).trace) := by
        ext i j
        simp [hgg]
      rw [hr, Matrix.det_reindex_self]
      exact hd

private theorem irr_iff_span {n : ℕ} {G K : Type} [Group G] [Field K] [IsAlgClosed K]
    (ρ : G →* Matrix (Fin n) (Fin n) K) :
    UpperTheory.V.U3.MatIrr ⊤ ρ ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  rw [← (UpperTheory.V.AlgebraTools.irred_iff_span (RingHom.id K) ρ).1]
  exact ⟨fun h N hN => h N fun g _ => hN g, fun h N hN => h N fun g => hN g (Subgroup.mem_top g)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.discStIff :
    ∀ {n : ℕ} {R G κ : Type} [CommRing R] [Group G] [Field κ] [IsAlgClosed κ] (D : GDet n R G) (f : R →+* κ), DiscSt D (RingHom.ker f) ↔ ∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ := by
  intro n R G κ _ _ _ _ D f
  have hQ : ∀ b, f b = 0 ↔ b ∈ RingHom.ker f := fun b => RingHom.mem_ker.symm
  constructor
  · intro h
    obtain ⟨ρ, -, hρ, -⟩ := UpperTheory.V.CA.groupDet_exists_semisimple_representation (D.map f)
    exact ⟨ρ, (irr_iff_span ρ).2 ((discSt_iff D f ρ hρ.symm _ hQ).1 h), hρ.symm⟩
  · rintro ⟨ρ, hirr, hρ⟩
    exact (discSt_iff D f ρ hρ _ hQ).2 ((irr_iff_span ρ).1 hirr)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OddPart
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem comb_entry {F G : Type} [Field F] {n m : ℕ} (r : G → Matrix (Fin n) (Fin n) F)
    (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (α β : Fin m → F) (c : G →₀ F) (i j : Fin n) :
    (c.sum fun g x => x • ((∑ k, α k • κ k g + ∑ k, β k • la k g) * r g)) i j =
      ∑ k, ((c.sum fun g x => x • (κ k g * r g)) i j * α k + (c.sum fun g x => x • (la k g * r g)) i j * β k) := by
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_mul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.add_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (s := c.support) (f := fun x k => c x * (α k * (κ k x * r x) i j)),
    Finset.sum_comm (s := c.support) (f := fun x k => c x * (β k * (la k x * r x) i j))]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem UpperTheory.V.Pa.Det.oddPart :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ k, ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, la k g = dTw D.χF D.r Y g := by
  intro F G _ _ n D m κ la s ph hK hT k
  classical
  by_cases ha : D.a < n
  · have hpos := D.a_pos
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨D.a, ha⟩
    have hij : ¬((i : ℕ) < D.a ↔ (j : ℕ) < D.a) := by
      intro h
      exact lt_irrefl D.a (h.mp (show (0 : ℕ) < D.a by omega))
    have hji : ¬((j : ℕ) < D.a ↔ (i : ℕ) < D.a) := fun h => hij h.symm
    have step1 : ∀ c' : G →₀ F, (∀ g ∈ c'.support, g ∈ D.G') → (c'.sum fun g x => x • D.r g) = 0 →
        ∀ k', (c'.sum fun g x => x • (la k' g * D.r g)) j i = 0 := by
      intro c' hc' hr'
      have hkill : D.KillsRel (fun g => ∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) i j := by
        intro c hc hr
        show (c.sum fun g x => x • ((∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) * D.r g)) i j = 0
        rw [comb_entry]
        exact Det.relPair D κ la s ph hK hT c c' hc hc' hr hr' i j hij
      have h := (Det.ann D κ la s ph hK hT _ _ i j hij hkill).1
      intro k'
      exact congrFun h k'
    have hkill2 : D.KillsRel (fun g => ∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) j i := by
      intro c hc hr
      show (c.sum fun g x => x • ((∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) * D.r g)) j i = 0
      rw [comb_entry]
      simp [step1 c hc hr]
    obtain ⟨_, Y, hY, hs, hg⟩ := Det.ann D κ la s ph hK hT 0 (Pi.single k 1) j i hji hkill2
    refine ⟨Y, hY, hs, fun g => ?_⟩
    rw [← hg g]
    simp [Pi.single_apply]
  · have han : D.a = n := le_antisymm D.a_le (not_lt.mp ha)
    refine ⟨0, Submodule.zero_mem _, by simp, fun g => ?_⟩
    have h0 : la k g = 0 := by
      ext i j
      have hm := (hT.od k g i j).1 (by rw [han]; exact iff_of_true i.2 j.2)
      exact (Submodule.mem_bot F).mp hm
    rw [h0]
    simp [dTw]
end

