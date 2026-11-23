module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.IsModel
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem liftMx {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (Z : Matrix (Fin n) (Fin n) K)
    (h : ∀ i j, ∃ a, f a = Z i j) : ∃ Z₀ : Matrix (Fin n) (Fin n) A, f.mapMatrix Z₀ = Z := by
  choose k hk using h
  refine ⟨Matrix.of fun i j => k i j, ?_⟩
  ext i j
  simp [RingHom.mapMatrix_apply, hk]

private theorem injM {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f) :
    Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) A → Matrix (Fin n) (Fin n) K) := by
  intro X X' hX
  ext i j
  apply hf
  have := congrFun (congrFun hX i) j
  simpa [RingHom.mapMatrix_apply] using this

private theorem liftU {A K : Type} [Monoid A] [Monoid K] (f : A →* K) (hf : Function.Injective f) (u : Kˣ)
    (h : ∃ a, f a = u) (h' : ∃ a, f a = (u⁻¹ : Kˣ)) : ∃ u₀ : Aˣ, Units.map f u₀ = u := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  refine ⟨⟨a, b, hf ?_, hf ?_⟩, ?_⟩
  · rw [map_mul, ha, hb, map_one]
    simp
  · rw [map_mul, ha, hb, map_one]
    simp
  · ext
    simp [ha]

private theorem liftG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f)
    (g : GL (Fin n) K) (h : ∀ i j, ∃ a, f a = (g : Matrix (Fin n) (Fin n) K) i j)
    (h' : ∀ i j, ∃ a, f a = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) :
    ∃ g₀ : GL (Fin n) A, GeneralLinearGroup.map f g₀ = g := by
  obtain ⟨a, ha⟩ := liftMx f _ h
  obtain ⟨b, hb⟩ := liftMx f _ h'
  obtain ⟨u, hu⟩ := liftU f.mapMatrix.toMonoidHom (injM f hf) g ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨u, Units.ext ?_⟩
  exact congrArg Units.val hu

private theorem liftH {H A B : Type} [Group H] [Group A] [Group B] (j : A →* B) (hj : Function.Injective j) (ρ : H →* B)
    (h : ∀ g, ∃ a, j a = ρ g) : ∃ ρ₀ : H →* A, j.comp ρ₀ = ρ := by
  choose k hk using h
  refine ⟨MonoidHom.mk' k (fun a b => hj (by rw [hk, map_mul, map_mul, hk, hk])), ?_⟩
  ext g
  show j (k g) = ρ g
  exact hk g

private theorem coeG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (g : GL (Fin n) A) :
    ((GeneralLinearGroup.map f g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f.mapMatrix (g : Matrix (Fin n) (Fin n) A) := rfl

private theorem injG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f) :
    Function.Injective (GeneralLinearGroup.map f : GL (Fin n) A → GL (Fin n) K) := by
  intro a b hab
  apply Units.ext
  apply injM f hf
  rw [← coeG, ← coeG, hab]

private theorem mapT {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (Z : Matrix (Fin n) (Fin n) A) :
    f.mapMatrix Zᵀ = (f.mapMatrix Z)ᵀ := rfl

private theorem mapS {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (a : A) (Z : Matrix (Fin n) (Fin n) A) :
    f.mapMatrix (a • Z) = f a • f.mapMatrix Z := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.smul_apply]

private theorem epsEq {l : ℕ} [Fact l.Prime] (F : GFrame l) (c₀ c : Coef l) (g : F.G₀) :
    F.eps c₀.O (Qbar l) g = Units.map (algebraMap c.O (Qbar l) : c.O →* Qbar l) (F.eps c.O c.O g) := by
  ext
  simp [GFrame.eps, pushCh]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.Nm.mkPt :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c₀ c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (w : F.Vl → GL (Fin n) (Qbar l)) (Y : F.Vl → Matrix (Fin n) (Fin n) (Qbar l)), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c₀.O n ρ P → ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ u, ∀ g ∈ F.Iu u, ρ g = 1) → (∀ v, ∃ g, Function.Injective fun i => ψ v i g) → (∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c₀.O (Qbar l)).comp (F.φ v)) → IsOrdCoc F ρ P F.Iu ψ z → (∀ v, OrdAt F ρ v (ψ v) z (w v) (Y v)) → (∀ g, InO c (mat ρ g)) → InO c (P : Matrix (Fin n) (Fin n) (Qbar l)) → InO c ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) → (∀ v, InO c (w v : Matrix (Fin n) (Fin n) (Qbar l)) ∧ InO c (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ InO c (Y v)) → (∀ g, InO c (z g)) → ∃ (y : Pt F c.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c.O), IsModel y ρ P ψ ∧ (∀ g, (z₀ g).map (algebraMap c.O (Qbar l)) = z g) ∧ OCoc y z₀ := by
  intro l _ n F c₀ c ρ P ψ z w Y hρc hspan hform hsgn hine hreg hN1 hz hord hρO hPO hPiO hwO hzO
  let ι : c.O →+* Qbar l := algebraMap c.O (Qbar l)
  have hι : Function.Injective ι := Subtype.val_injective
  have lift1 : ∀ Z : Matrix (Fin n) (Fin n) (Qbar l), InO c Z → ∀ i j, ∃ a, ι a = Z i j :=
    fun Z hZ i j => ⟨⟨Z i j, hZ i j⟩, rfl⟩
  have hGL : ∀ g : GL (Fin n) (Qbar l), InO c (g : Matrix (Fin n) (Fin n) (Qbar l)) →
      InO c ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) →
      ∃ g₀ : GL (Fin n) c.O, GeneralLinearGroup.map ι g₀ = g :=
    fun g h1 h2 => liftG ι hι g (lift1 _ h1) (lift1 _ h2)
  have hρO' : ∀ g, InO c ((ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := hρO
  obtain ⟨ρ₀, hρ₀⟩ := liftH (GeneralLinearGroup.map ι) (injG ι hι) ρ
    (fun g => hGL (ρ g) (hρO' g) (by rw [← map_inv]; exact hρO' g⁻¹))
  have hρx : ∀ x, GeneralLinearGroup.map ι (ρ₀ x) = ρ x := fun x => DFunLike.congr_fun hρ₀ x
  obtain ⟨P₀, hP₀⟩ := hGL P hPO hPiO
  choose w₀ hw₀ using fun v => hGL (w v) (hwO v).1 (hwO v).2.1
  choose Y₀ hY₀ using fun v => liftMx ι (Y v) (lift1 _ (hwO v).2.2)
  choose z₀ hz₀ using fun g => liftMx ι (z g) (lift1 _ (hzO g))
  have heq : ∀ (A : Matrix (Fin n) (Fin n) c.O) (B : Matrix (Fin n) (Fin n) (Qbar l)),
      ι.mapMatrix A = B → ∀ i j, ι (A i j) = B i j := by
    intro A B hAB i j
    rw [← hAB]
    rfl
  have hz0 : ∀ (A : Matrix (Fin n) (Fin n) c.O) (B : Matrix (Fin n) (Fin n) (Qbar l)),
      ι.mapMatrix A = B → ∀ i j, B i j = 0 → A i j = 0 := by
    intro A B hAB i j hB
    apply hι
    rw [map_zero, heq A B hAB i j, hB]
  have hmρ : ∀ x, ι.mapMatrix (mat ρ₀ x) = mat ρ x := by
    intro x
    show ι.mapMatrix ((ρ₀ x : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) = ((ρ x : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))
    rw [← hρx x, coeG]
  have hmP : ι.mapMatrix (P₀ : Matrix (Fin n) (Fin n) c.O) = P := by
    rw [← hP₀, coeG]
  have hmw : ∀ v, ι.mapMatrix (w₀ v : Matrix (Fin n) (Fin n) c.O) = w v := by
    intro v
    rw [← hw₀ v, coeG]
  have hmwi : ∀ v, ι.mapMatrix (((w₀ v)⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) =
      (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v
    rw [← coeG, map_inv, hw₀ v]
  have hconj : ∀ v g, GeneralLinearGroup.map ι ((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v) =
      (w v)⁻¹ * ρ (F.φ v g) * w v := by
    intro v g
    rw [map_mul, map_mul, map_inv, hw₀ v, hρx]
  have hψval : ∀ v i g, ∃ a, ι a = ((ψ v i g : (Qbar l)ˣ) : Qbar l) := by
    intro v i g
    refine ⟨(((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) i i, ?_⟩
    rw [← ((hord v g).2.1 i), ← hconj v g, coeG]
    rfl
  choose ψ₀ hψ₀ using fun v i => liftH (Units.map ι.toMonoidHom) (Units.map_injective hι) (ψ v i)
    (fun g => liftU ι.toMonoidHom hι (ψ v i g) (hψval v i g) (by rw [← map_inv]; exact hψval v i g⁻¹))
  have hψx : ∀ v i g, Units.map ι.toMonoidHom (ψ₀ v i g) = ψ v i g := fun v i g => DFunLike.congr_fun (hψ₀ v i) g
  have hmz : ∀ g, ι.mapMatrix (z₀ g) = z g := hz₀
  have hdY : ∀ v x, ι.mapMatrix (dY F (mat ρ₀) (Y₀ v) x) = dY F (mat ρ) (Y v) x := by
    intro v x
    simp only [dY, map_sub, map_mul, hmρ, hY₀]
  have hbig : ∀ v x, ι.mapMatrix ((((w₀ v)⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) *
      (z₀ x - dY F (mat ρ₀) (Y₀ v) x) * (w₀ v : Matrix (Fin n) (Fin n) c.O)) =
      (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
      (z x - dY F (mat ρ) (Y v) x) * (w v : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v x
    rw [map_mul, map_mul, map_sub, hmwi, hmz, hdY, hmw]
  have hcont : ∀ f : F.G₀ → c.O, Continuous (fun g => ι (f g)) → AdicCont (maximalIdeal c.O) f :=
    fun f hf => (inOf c).2.2.2 F.G₀ f hf
  have hcM : ∀ v g, ι.mapMatrix ((((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v : GL (Fin n) c.O)) : Matrix (Fin n) (Fin n) c.O) =
      (((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v g
    rw [← coeG, hconj v g]
  refine ⟨Th.Pt.mk ρ₀ ?_ P₀ ?_ ?_ ?_ ?_ ψ₀ w₀ ?_ ?_ ?_, z₀, ⟨hρ₀, hP₀, fun v i => hψ₀ v i⟩, fun g => hz₀ g, ?_⟩
  · intro i j
    apply hcont
    have : (fun g => ι (mat ρ₀ g i j)) = fun g => mat ρ g i j := by
      funext g
      exact heq _ _ (hmρ g) i j
    rw [this]
    exact (Units.continuous_val.comp hρc).matrix_elem i j
  · rcases hsgn with h | h
    · left
      apply injM ι hι
      rw [mapT, hmP, h]
    · right
      apply injM ι hι
      rw [mapT, hmP, h, map_neg, hmP]
  · intro g
    apply injM ι hι
    rw [map_mul, map_mul, mapT, hmρ, hmρ, hmP, mapS, hmP, hform g, epsEq F c₀ c g, ← map_zpow]
    rfl
  · obtain ⟨a, ha, hZ⟩ := spanO c F.G₀ (mat ρ₀) (by
      have : (fun g => (mat ρ₀ g).map (algebraMap c.O (Qbar l))) = fun g => mat ρ g := funext hmρ
      rw [this]
      exact hspan)
    exact ⟨a, ha, hZ⟩
  · intro u g hg
    apply injG ι hι
    rw [hρx, map_one, hine u g hg]
  · intro v g
    refine ⟨fun i j hij => hz0 _ _ (hcM v g) i j ((hord v g).1 i j hij), fun i => ?_⟩
    apply hι
    rw [heq _ _ (hcM v g) i i, (hord v g).2.1 i]
    exact (congrArg Units.val (hψx v i g)).symm
  · intro v
    obtain ⟨g, hg⟩ := hreg v
    refine ⟨g, fun i j hij => hg ?_⟩
    show ψ v i g = ψ v j g
    rw [← hψx v i g, ← hψx v j g]
    exact congrArg _ hij
  · intro v i j hij hE
    apply hN1 v i j hij
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, ← hψx v i g, ← hψx v j g, epsEq F c₀ c, hE]
    rfl
  · refine ⟨fun i j => ?_, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ⟨Y₀ v, fun g => ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · apply hcont
      have : (fun g => ι (z₀ g i j)) = fun g => z g i j := by
        funext g
        exact heq _ _ (hmz g) i j
      rw [this]
      exact hz.cont.matrix_elem i j
    · apply injM ι hι
      show ι.mapMatrix (z₀ (g * g')) = ι.mapMatrix (z₀ g + mat ρ₀ g * z₀ g' * mat ρ₀ g⁻¹)
      rw [map_add (f := _), map_mul, map_mul, hmz, hmz, hmz, hmρ, hmρ, hz.coc]
    · apply injM ι hι
      show ι.mapMatrix ((P₀ : Matrix (Fin n) (Fin n) c.O) * z₀ (F.conj g)) = ι.mapMatrix (-((z₀ g)ᵀ * (P₀ : Matrix (Fin n) (Fin n) c.O)))
      rw [map_mul, map_neg, map_mul, mapT, hmP, hmz, hmz, hz.pol]
    · apply injM ι hι
      rw [hmz, map_zero, hz.ine u g hg]
    · exact fun i j hij => hz0 _ _ (hcM v g) i j ((hord v g).1 i j hij)
    · intro i
      apply hι
      rw [heq _ _ (hcM v g) i i, (hord v g).2.1 i]
      exact (congrArg Units.val (hψx v i g)).symm
    · exact fun i j hij => hz0 _ _ (hbig v _) i j ((hord v g).2.2.1 i j hij)
    · exact fun hg i => hz0 _ _ (hbig v _) i i ((hord v g).2.2.2 hg i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.LocalOfFinite
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem local_of_finite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] (f : R →+* S) : IsLocalHom f := by
  classical
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  let g : R →+* ResidueField S := (residue S).comp f
  have hker : RingHom.ker g = maximalIdeal R := by
    haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
    haveI : Finite (R ⧸ RingHom.ker g) := Finite.of_injective _ (RingHom.kerLift_injective g)
    have hmax : (RingHom.ker g).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
    exact IsLocalRing.eq_maximalIdeal hmax
  have hg : g a = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hm
  have hfa : f a ∈ maximalIdeal S := by
    simpa [g, residue_eq_zero_iff] using hg
  exact hfa ha

theorem UpperTheory.V.Th.Nm.redOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (p : Pair r R) (x : R →ₐ[c.O] Qbar l) (ρ₀ : F.G₀ →* GL (Fin n) c'.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c'.Oˣ), RPush h r r' → (∀ b, x b ∈ c'.O) → p.D.map (x : R →+* Qbar l) = GDet.ofRep (mat (pushRep (algebraMap c'.O (Qbar l)) ρ₀)) → (∀ v i, pushCh (algebraMap c'.O (Qbar l)) (ψ₀ v i) = pushCh (x : R →+* Qbar l) (p.ψ v i)) → (GDet.ofRep (mat ρ₀)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = r'.Dbar ∧ ∀ v i, r'.IsPsi v i (ψ₀ v i) := by
  intro l _ n F c c' h r r' R _ _ _ p x ρ₀ ψ₀ hpush hx hD hψ
  haveI : Module.Finite ℤ_[l] c'.O := c'.fin
  haveI : Finite (ResidueField c'.O) := (abelian₂.dvr_finite l c'.O).2.1
  obtain ⟨f, hf, hchi, hpsi, hth⟩ := hpush
  let ι : c'.O →+* Qbar l := algebraMap c'.O (Qbar l)
  have hι : Function.Injective ι := Subtype.val_injective
  let y : R →+* c'.O := (x : R →+* Qbar l).codRestrict c'.O hx
  have hy : ι.comp y = (x : R →+* Qbar l) := by
    ext z
    rfl
  haveI : IsLocalHom y := local_of_finite y
  have hyalg : ∀ a : c.O, y (algebraMap c.O R a) = inc h a := by
    intro a
    apply hι
    show x (algebraMap c.O R a) = ι (inc h a)
    rw [x.commutes]
    rfl
  have hym : ∀ z ∈ maximalIdeal R, y z ∈ maximalIdeal c'.O := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hz ((isUnit_map_iff y _).1 hu)
  have hres : ∀ z, residue c'.O (y z) = f (res c.O R z) := by
    intro z
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) z
    have hz : z = algebraMap c.O R a + (z - algebraMap c.O R a) := by ring
    have hm0 : res c.O R (z - algebraMap c.O R a) = 0 := by
      simp [UpperTheory.V.Alg.res, (IsLocalRing.residue_eq_zero_iff _).2 ha]
    have hm1 : residue c'.O (y (z - algebraMap c.O R a)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 (hym _ ha)
    rw [hz, map_add (f := _), map_add (f := _), map_add (f := _), hm1, hm0, hyalg, AlgHom.commutes, ← hf]
    simp [ResidueField.algebraMap_eq]
  have hresid : ∀ w : c'.O, res c'.O c'.O w = residue c'.O w := by
    intro w
    have := (res c'.O c'.O).commutes w
    simpa [ResidueField.algebraMap_eq] using this
  have hresring : (res c'.O c'.O : c'.O →+* ResidueField c'.O) = residue c'.O := by
    ext w
    exact hresid w
  have hmapeq : (GDet.ofRep (mat ρ₀)).map ι = (p.D.map y).map ι := by
    rw [(CA.d_gmap (p.D)).2.1 y ι, hy, hD, (CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.2 ι (mat ρ₀)]
    congr 1
  have hρ : GDet.ofRep (mat ρ₀) = p.D.map y := by
    apply CA.d_gext
    intro g i _ _
    apply hι
    have e1 := ((CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap (p.D.map y)).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    rw [← e1, ← e2, hmapeq]
  have hψy : ∀ v i g, ((ψ₀ v i g : c'.Oˣ) : c'.O) = y (p.ψ v i g : R) := by
    intro v i g
    apply hι
    have := congrArg (fun φ : F.Gv v →* (Qbar l)ˣ => ((φ g : (Qbar l)ˣ) : Qbar l)) (hψ v i)
    exact this
  refine ⟨?_, ?_⟩
  · rw [hρ, (CA.d_gmap p.D).2.1, hresring]
    have hcomp : (residue c'.O).comp y = f.comp (res c.O R : R →+* ResidueField c.O) := by
      ext z
      exact hres z
    rw [hcomp, ← (CA.d_gmap p.D).2.1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map f = GDet.ofRep (diagRep r'.chib)
    rw [(CA.d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2 f (diagRep r.chib)]
    congr 1
    ext g i j
    simp only [MonoidHom.coe_comp, Function.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk,
      RingHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, hchi]
    split_ifs with hij <;> simp [hij, Matrix.diagonal_apply]
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hym) N
      have hc := (p.psi v i).cont N
      have : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((ψ₀ v i g : c'.Oˣ) : c'.O)) =
          (Ideal.quotientMap (maximalIdeal c'.O ^ N) y hle) ∘
            (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) ((p.ψ v i g : Rˣ) : R)) := by
        funext g
        simp [hψy, Ideal.quotientMap_mk]
      rw [this]
      exact hc.comp _
    · intro g
      rw [hresid, hψy, hres, (p.psi v i).red, hpsi]
      rfl
    · intro g
      rw [hψy, (p.psi v i).mu, hyalg, hth]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Midpoint
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem intM_mul' {l : ℕ} [Fact l.Prime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) (hB : IntM B) : IntM (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private theorem intM_transpose' {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) : IntM Aᵀ := fun i j => hA j i

private theorem le_one_of_mul_self {x : ℝ} (h : x * x ≤ 1) : x ≤ 1 := by nlinarith

private theorem intM_of_symm {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hs : (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = diagonal (fun i => (e i)⁻¹) * A * diagonal e ∨
      (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = -(diagonal (fun i => (e i)⁻¹) * A * diagonal e)) :
    IntM (diagonal (fun i => (e i)⁻¹) * A * diagonal e) := by
  intro i j
  set M := diagonal (fun i => (e i)⁻¹) * A * diagonal e with hM
  have hent : ∀ a b, M a b = (e a)⁻¹ * A a b * e b := by
    intro a b
    rw [hM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hn : ‖M j i‖ = ‖M i j‖ := by
    rcases hs with h | h
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply] at this
      rw [this]
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this, norm_neg]
  have hp : M i j * M j i = A i j * A j i := by
    rw [hent, hent]
    have := he i
    have := he j
    field_simp
  apply le_one_of_mul_self
  calc ‖M i j‖ * ‖M i j‖ = ‖M i j * M j i‖ := by rw [norm_mul, hn]
    _ = ‖A i j‖ * ‖A j i‖ := by rw [hp, norm_mul]
    _ ≤ 1 := mul_le_one₀ (hA i j) (norm_nonneg _) (hA j i)

private theorem intM_mid {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hB : IntM (diagonal e * diagonal e * A * diagonal (fun i => (e i)⁻¹) * diagonal (fun i => (e i)⁻¹))) :
    IntM (diagonal e * A * diagonal (fun i => (e i)⁻¹)) := by
  intro i j
  have h1 := hB i j
  rw [Matrix.mul_assoc (diagonal e) (diagonal e), Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_mul] at h1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply le_one_of_mul_self
  have hp : (e i * A i j * (e j)⁻¹) * (e i * A i j * (e j)⁻¹)
      = (e i * (e i * A i j) * (e j)⁻¹ * (e j)⁻¹) * A i j := by ring
  rw [← norm_mul, hp, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) (hA i j)

private theorem inv_symm {K : Type} [CommRing K] {n : ℕ} (M : GL (Fin n) K)
    (h : (M : Matrix (Fin n) (Fin n) K)ᵀ = M ∨ (M : Matrix (Fin n) (Fin n) K)ᵀ = -M) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (M⁻¹ : GL (Fin n) K) ∨
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = -((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : (M : Matrix (Fin n) (Fin n) K) * (M⁻¹ : GL (Fin n) K) = 1 := M.mul_inv
  generalize ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N at h1 ⊢
  generalize (M : Matrix (Fin n) (Fin n) K) = A at h h1
  have h2 : Nᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rcases h with h | h
  · left
    rw [h] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  · right
    rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = -N := by rw [← Matrix.mul_assoc, h2, Matrix.neg_mul, Matrix.one_mul]

theorem UpperTheory.V.Th.Nm.midpoint :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (S : Set (GL (Fin n) (Qbar l))) (P : GL (Fin n) (Qbar l)), ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ g ∈ S, IntM (g : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P * g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g ∈ S, IntM ((Q⁻¹ * g * Q : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
  intro l _ n S P hP hS
  obtain ⟨U, V, d, hU, hU', hV, hV', hd, hPe⟩ := smith P
  have hsq : ∀ i, ∃ z : Qbar l, d i = z * z := fun i => IsAlgClosed.exists_eq_mul_self (d i)
  choose e hee using hsq
  have he : ∀ i, e i ≠ 0 := fun i h => hd i (by rw [hee i, h, mul_zero])
  obtain ⟨E, hE, hE'⟩ : ∃ E : GL (Fin n) (Qbar l), (E : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal e ∧
      ((E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal (fun i => (e i)⁻¹) := by
    refine ⟨⟨diagonal e, diagonal (fun i => (e i)⁻¹), ?_, ?_⟩, rfl, rfl⟩
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact mul_inv_cancel₀ (he i)
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact inv_mul_cancel₀ (he i)
  obtain ⟨T, hT, hT'⟩ : ∃ T : GL (Fin n) (Qbar l),
      (T : Matrix (Fin n) (Fin n) (Qbar l)) = (V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ ∧
      ((T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
        ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ := by
    refine ⟨⟨(V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, ?_, ?_⟩, rfl, rfl⟩
    · rw [← Matrix.transpose_mul, V.inv_mul, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, V.mul_inv, Matrix.transpose_one]
  have hPG : P = U * (E * E) * V := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hE, Matrix.diagonal_mul_diagonal, hPe]
    congr 3; funext i; exact hee i
  have hQt : ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ
      = ((E⁻¹ * T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [Units.val_mul, Units.val_mul, Matrix.transpose_mul, hT', hE', Matrix.diagonal_transpose]
  have hP' : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P *
        ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hQt, ← Units.val_mul, ← Units.val_mul, hPG]
    congr 1
    group
  have hsym : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∨
      ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        -((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    rcases hP with h | h
    · left; rw [h]
    · right; rw [h, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨V⁻¹ * E⁻¹, E⁻¹ * (T⁻¹ * U) * E, hP', ?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hE, hE'] at hsym ⊢
    refine intM_of_symm e he ?_ hsym
    rw [Units.val_mul, hT']
    exact intM_mul' (intM_transpose' hV') hU
  · have hi := inv_symm _ hsym
    have hinv : (E⁻¹ * (T⁻¹ * U) * E)⁻¹ = E⁻¹ * (U⁻¹ * T) * E := by group
    rw [hinv, Units.val_mul, Units.val_mul, hE, hE'] at hi ⊢
    refine intM_of_symm e he ?_ hi
    rw [Units.val_mul, hT]
    exact intM_mul' hU' (intM_transpose' hV)
  · intro g hg
    obtain ⟨h1, h2⟩ := hS g hg
    have e1 : (V⁻¹ * E⁻¹)⁻¹ * g * (V⁻¹ * E⁻¹) = E * (V * g * V⁻¹) * E⁻¹ := by group
    have e2 : E * E * (V * g * V⁻¹) * E⁻¹ * E⁻¹ = U⁻¹ * (P * g * P⁻¹) * U := by
      rw [hPG]; group
    rw [e1, Units.val_mul, Units.val_mul, hE, hE']
    refine intM_mid e he ?_ ?_
    · rw [Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hV h1) hV'
    · rw [← hE, ← hE', ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, e2,
        Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hU' h2) hU
end

