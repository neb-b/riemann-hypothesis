module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.PairOfRep
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
open UpperTheory.V.AlgebraTools.Det

private theorem pairOfRep_cont {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (h : ∀ a b, AdicCont I fun g => ρ g a b) : (GDet.ofRep ρ).IsCont I := by
  intro i N
  have hl : IsLocallyConstant (fun g : G => fun a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    letI : TopologicalSpace (A ⧸ I ^ N) := ⊥
    haveI : DiscreteTopology (A ⧸ I ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun a => continuous_pi fun b => (IsLocallyConstant.iff_continuous _).1 (h a b N)
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))) =
      (fun M : Fin n → Fin n → A ⧸ I ^ N =>
        Ideal.Quotient.mk (I ^ N) ((-1 : A) ^ i) * (Matrix.of M).charpoly.coeff (n - i)) ∘
        (fun g a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    funext g
    simp only [Function.comp_apply, GDet.lam, (repApi ρ).2.1, map_mul]
    congr 1
    rw [← Polynomial.coeff_map, ← Matrix.charpoly_map]
    rfl
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1)))
  rw [key]
  exact hl.comp _

private theorem pairOfRep_polar {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type)
    [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (P : GL (Fin n) R) (h : F.IsForm O n r P) (i : ℕ)
    (y : MonoidAlgebra R F.G₀) : (GDet.ofRep (mat r)).lam i (F.star O R n y) = (GDet.ofRep (mat r)).lam i y := by
  have key := (formRep F O R n r P h).1 R y
  have hP : (↑P : Matrix (Fin n) (Fin n) R).map ⇑(algebraMap R R) = ↑P := by
    ext a b
    simp
  rw [hP] at key
  have e : (GDet.repAlg (mat r) R) (F.star O R n y) =
      ((P⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((GDet.repAlg (mat r) R) y)ᵀ *
        ((P⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [inv_inv, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  unfold GDet.lam
  rw [(repApi (mat r)).1, (repApi (mat r)).1, e, Matrix.coe_units_inv (P⁻¹), Matrix.charpoly_units_conj,
    Matrix.charpoly_transpose]

theorem UpperTheory.V.Th.Nm.pairOfRep :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (ρ : F.G₀ →* GL (Fin n) A) (P : GL (Fin n) A) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ), 1 ≤ n → (∀ i j, AdicCont (maximalIdeal A) fun g => mat ρ g i j) → (GDet.ofRep (mat ρ)).map (res O A : A →+* ResidueField O) = r.Dbar → F.IsForm O n ρ P → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ v, HasFlag (ρ.comp (F.φ v)) (ψ v)) → (∀ u, ∀ g ∈ r.Ip u, ρ g = 1) → ∃ p : Pair r A, p.D = GDet.ofRep (mat ρ) ∧ p.ψ = ψ := by
  intro l _ n F O _ _ _ r A _ _ _ ρ P ψ hn hc hred hP hψ hfl hI
  refine ⟨⟨GDet.ofRep (mat ρ), ψ, pairOfRep_cont _ _ hc, hred, hψ, fun i g => pairOfRep_polar F O A n ρ P hP i _,
    fun v g h => ?_, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h2 := oElRep F O A n ρ v _ (hfl v) g
    rw [(repApi _).2.2.1 hn, map_mul, h2, mul_zero, Matrix.trace_zero]
  · have h1 : GDet.repAlg (mat ρ) A (MonoidAlgebra.single g 1 - 1) = 0 := by
      rw [map_sub, map_one]
      simp [GDet.repAlg, mat, hI u g hg]
    rw [(repApi _).2.2.1 hn, map_mul, h1, mul_zero, Matrix.trace_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RegArith
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem norm_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  have key : ∀ t, ‖(ψ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h2

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem emb_ne (H : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion L)ˣ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) :
    Nonempty (Emb l w) := by
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * Hi.algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  by_contra hE
  haveI : IsEmpty (Emb l w) := not_nonempty_iff.1 hE
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
  rw [hε, deg_frob, zpow_one, Hi.algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
  have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
    have := one_lt_normV w
    rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
    exact lt_irrefl _ this)).1 h1
  exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {w : Plc F} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {a : Weil h →* (w.adicCompletion F)ˣ} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {n : ℕ}
    (wt : Fin n → Emb l w → ℤ) (hm : ∀ τ, StrictMono fun j => wt j τ) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ)
    (hψ : ∀ j, IsLocAlg h (ψ j) (wt j)) : ∃ g, Function.Injective fun i => ψ i g := by
  haveI := emb_ne H hw ha
  haveI : Finite (Emb l w) := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (Emb l w)
  haveI : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  choose ph hph using hψ
  let U : Subgroup (Ine (F := F) A) := ⨅ j, (ph j).ker
  have hU : IsOpen (U : Set (Ine (F := F) A)) := by
    simp only [U, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => (hph j).1
  haveI : Finite (Ine (F := F) A ⧸ U) := U.quotient_finite_of_isOpen hU
  have hN : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hl : ValuativeRel.valuation (w.adicCompletion F) (l : w.adicCompletion F) < 1 := by
    have e : (ValuativeRel.valuation (w.adicCompletion F)).IsEquiv (Valued.v : Valuation (w.adicCompletion F) _) := by
      haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion F) _)
      exact ValuativeRel.isEquiv _ _
    rw [e.lt_one_iff_lt_one, ← map_natCast (algebraMap (𝓞 F) (w.adicCompletion F)),
      IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
    erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem _).2 hw
  have hu : ValuativeRel.valuation (w.adicCompletion F) (1 + l : w.adicCompletion F) = 1 :=
    (ValuativeRel.valuation (w.adicCompletion F)).map_one_add_of_lt hl
  have hu0 : (1 + l : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at hu
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 _ hu0)
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at h2
    omega
  have hI : (s : G F Ω) ∈ Ine (F := F) A := actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))
  let σ : Ine (F := F) A := ⟨s, hI⟩
  haveI : U.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hmem : σ ^ U.index ∈ U := U.pow_index_mem σ
  have e : ((a (ineIncl h (σ ^ U.index)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = (1 + l) ^ U.index := by
    rw [map_pow, map_pow, show ineIncl h σ = s from rfl, hs]
    simp
  let q : ℕ := (1 + l) ^ U.index
  have hq : 1 < q := Nat.one_lt_pow hN (by have := (Fact.out : l.Prime).pos; omega)
  have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp : ∀ (T : Finset (Emb l w)) (c : Emb l w → ℤ), ∏ j ∈ T, (q : Qbar l) ^ c j = (q : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hq0]
  have key : ∀ j, ((ψ j (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index))) : (Qbar l)ˣ) : Qbar l) =
      (q : Qbar l) ^ ∑ τ, -wt j τ := fun j => by
    have h3 := (hph j).2 a ha (σ ^ U.index)
    rw [show ph j (σ ^ U.index) = 1 from Subgroup.mem_iInf.1 hmem j, finprod_eq_prod_of_fintype, e, mul_one] at h3
    rw [h3, ← hp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [q]
  refine ⟨Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index)), fun i j hij => ?_⟩
  have h4 : (q : Qbar l) ^ ∑ τ, -wt i τ = (q : Qbar l) ^ ∑ τ, -wt j τ := by
    rw [← key, ← key]
    exact congrArg Units.val hij
  have h5 : (q : ℚ) ^ ∑ τ, -wt i τ = (q : ℚ) ^ ∑ τ, -wt j τ := by
    apply Rat.cast_injective (α := Qbar l)
    simpa using h4
  have h6 := zpow_right_injective₀ (a := (q : ℚ)) (by positivity) (by exact_mod_cast hq.ne') h5
  have hs : StrictAnti fun j => ∑ τ, -wt j τ := fun i j hij =>
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ _ => neg_lt_neg (hm τ hij)
  exact hs.injective h6

theorem UpperTheory.V.Th.Nm.regArith :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (h : s.Wt n) (v : Vl l L) (ψ : Fin n → Dec (F := L) (s.A v) →* (Qbar l)ˣ), h.Incr → (∀ j, IsLocAlg (s.hw v) (ψ j) (h v j)) → ∃ g, Function.Injective fun i => ψ i g := by
  intro H l _ L Ω _ _ _ _ _ _ s n h v ψ hI hψ
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.localArtinReciprocity H (s.hw v)
  have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
  exact main H.aut.art (s.hw v) ((s.hw v.1 _).1 (by simpa using h1)) ha (h v) (hI v) ψ hψ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ResidPush
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inc_local {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : IsLocalHom (inc h) := by
  have hint : (inc h).IsIntegral := by
    have h0 : (algebraMap ℤ_[l] c'.O).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := by
      ext a; rfl
    rw [← e] at h0
    exact RingHom.IsIntegral.tower_top _ _ h0
  exact RingHom.IsIntegral.isLocalHom hint (Subalgebra.inclusion_injective h)

private theorem pushCh_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hg
    apply Units.ext
    apply hf
    have := congrArg Units.val hg
    simpa using this
  · intro hg
    rw [hg, map_one]

private theorem polar_push {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {O O' k k' : Type} [CommRing O] [CommRing O']
    [CommRing k] [CommRing k'] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [Algebra O k] [Algebra O' k']
    (i : O →+* O') (f : k →+* k') (hi : ∀ a, i (algebraMap ℤ_[l] O a) = algebraMap ℤ_[l] O' a)
    (hf : ∀ a, f (algebraMap O k a) = algebraMap O' k' (i a)) (χ : Fin n → F.G₀ →* kˣ)
    (hp : F.IsPolar O (GDet.ofRep (diagRep χ))) :
    F.IsPolar O' (GDet.ofRep (diagRep fun j => pushCh f (χ j))) := by
  intro B _ _ _ _ y
  letI : Algebra k B := ((algebraMap k' B).comp f).toAlgebra
  letI : Algebra O B := ((algebraMap O' B).comp i).toAlgebra
  haveI : IsScalarTower O k B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap O' B (i a) = algebraMap k' B (f (algebraMap O k a))
    rw [hf, ← IsScalarTower.algebraMap_apply]
  have he : F.eps O' B = F.eps O B := by
    unfold GFrame.eps
    congr 1
    ext a
    change algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (i (algebraMap ℤ_[l] O a))
    rw [hi]
  have hs : F.star O' B n y = F.star O B n y := by
    unfold GFrame.star GFrame.starOp
    simp only [he]
  have hr : GDet.repAlg (diagRep fun j => pushCh f (χ j)) B = GDet.repAlg (diagRep χ) B := by
    unfold GDet.repAlg
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [diagRep]
      rfl
    · simp [diagRep, hab]
  have := hp B y
  change (GDet.repAlg (diagRep χ) B _).det = (GDet.repAlg (diagRep χ) B _).det at this
  change (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det = (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det
  rw [hr, hs]
  exact this

theorem UpperTheory.V.Th.Nm.residPush :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n), ∃ r' : Resid F c'.O n, RPush h r r' ∧ (∀ u, r'.Ip u = r.Ip u) ∧ (r.V0ok → r'.V0ok) := by
  intro l _ n F c c' h r
  haveI := inc_local h
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map (inc h)
  have hfi : Function.Injective f := f.injective
  have hf : ∀ a, f (residue c.O a) = residue c'.O (inc h a) := fun a => ResidueField.map_residue _ a
  refine ⟨{ chib := fun i => pushCh f (r.chib i)
            chib_open := fun i => by rw [pushCh_ker f hfi]; exact r.chib_open i
            chib_inj := fun i j hij => r.chib_inj ?_
            polar := polar_push F (inc h) f (fun _ => rfl) hf r.chib r.polar
            psib := fun v i => pushCh f (r.psib v i)
            psib_open := fun v i => by rw [pushCh_ker f hfi]; exact r.psib_open v i
            th := fun v i => pushCh (inc h) (r.th v i)
            th_comm := fun v i g hg => by
              rw [MonoidHom.comp_apply, r.th_comm v i g hg, map_one] },
    ⟨f, hf, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun u => ?_, fun hv => ⟨fun i => ?_, fun g hg i j => ?_, ?_⟩⟩
  · ext g
    apply hfi
    have := congrArg Units.val (DFunLike.congr_fun hij g)
    simpa using this
  · simp only [Resid.Ip, pushCh_ker f hfi]
  · rw [pushCh_ker f hfi]; exact hv.1 i
  · change Units.map _ (r.chib i g) = Units.map _ (r.chib j g)
    rw [hv.2.1 g hg i j]
  · obtain ⟨g, hg, hne⟩ := hv.2.2
    refine ⟨g, hg, fun e => hne ?_⟩
    apply Units.ext
    apply hfi
    have := congrArg Units.val e
    rw [Units.val_one, map_one]
    exact (hf _).trans this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RootsNormLe
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.roots_norm_le {l : ℕ} [Fact l.Prime] {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) (Qbar l)) (hZ : IntM Z) (a : Qbar l) (ha : Z.charpoly.IsRoot a) :
    ‖a‖ ≤ 1 := by
  classical
  have hdet : (Matrix.scalar (Fin n) a - Z).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact ha
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hc
    apply hv0
    funext j
    exact absurd ⟨j, Finset.mem_univ j⟩ hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) hne
  have hvi : v i ≠ 0 := by
    intro h0
    apply hv0
    funext j
    have hj := hi j (Finset.mem_univ j)
    rw [h0, norm_zero] at hj
    exact norm_le_zero_iff.1 hj
  have heq : a * v i = ∑ j, Z i j * v j := by
    have hvi' := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.zero_apply,
      sub_eq_zero] at hvi'
    rw [hvi']
    rfl
  have hle : ‖a‖ * ‖v i‖ ≤ 1 * ‖v i‖ := by
    rw [← norm_mul, heq, one_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    exact (mul_le_mul (hZ i j) (hi j (Finset.mem_univ j)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hvi)

theorem UpperTheory.V.Th.Nm.roots :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (Z : Matrix (Fin n) (Fin n) (Qbar l)), IntM Z → Z.charpoly.Separable → ∃ al : Fin n → Qbar l, Function.Injective al ∧ (∀ i, ‖al i‖ ≤ 1) ∧ Z.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) := by
  intro l _ n Z hZ hsep
  classical
  set p := Z.charpoly with hp
  set s := p.roots.toFinset with hs
  have hnd : p.roots.Nodup := Polynomial.nodup_roots hsep
  have hval : s.val = p.roots := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  have hcard : s.card = n := by
    rw [← Finset.card_val, hval, IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  let e : Fin n ≃ s := (finCongr hcard.symm).trans s.equivFin.symm
  refine ⟨fun i => (e i : Qbar l), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    have hmem : (e i : Qbar l) ∈ p.roots := by
      rw [← hval]
      exact (e i).2
    exact roots_norm_le Z hZ _ (Polynomial.isRoot_of_mem_roots hmem)
  · rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic (Matrix.charpoly_monic Z), ← hval,
      ← Finset.prod_eq_multiset_prod, ← Finset.prod_coe_sort s]
    exact (Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : Qbar l))).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SgConjConj
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l)

private theorem sg_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

private theorem sg_eps_conj (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε (F.c * g * F.c⁻¹) = F.ε g := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact congrArg (Units.map (((algebraMap O R).comp (algebraMap ℤ_[l] O) : ℤ_[l] →+* R) : ℤ_[l] →* R)) h

end

private theorem sg_comm {K : Type} [Field K] {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) K) (e : K) (hA : IsUnit A)
    (hP : IsUnit P) (hQ : P * Q = 1) (h1 : Aᵀ * P * B = e • P) (h2 : Bᵀ * P * A = e • P) :
    B * (Q * Pᵀ) = (Q * Pᵀ) * B := by
  have h3 : Aᵀ * Pᵀ * B = e • Pᵀ := by
    have := congrArg transpose h2
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_smul, ← mul_assoc] at this
  have hu : IsUnit (Aᵀ * P) := ((isUnit_transpose A).2 hA).mul hP
  apply hu.mul_left_cancel
  calc Aᵀ * P * (B * (Q * Pᵀ)) = (Aᵀ * P * B) * Q * Pᵀ := by simp only [mul_assoc]
    _ = e • Pᵀ := by rw [h1, smul_mul_assoc, hQ, smul_mul_assoc, one_mul]
    _ = Aᵀ * (P * Q) * Pᵀ * B := by rw [hQ, mul_one, h3]
    _ = Aᵀ * P * (Q * Pᵀ * B) := by simp only [mul_assoc]

private theorem sg_end {K : Type} [Field K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (hQ : P * Q = 1)
    (h : ∀ Z : Matrix (Fin n) (Fin n) K, Z * (Q * Pᵀ) = (Q * Pᵀ) * Z) : Pᵀ = P ∨ Pᵀ = -P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_single (M := Q * Pᵀ) (fun i j _ => h _)
  have h1 : Pᵀ = s • P := by
    calc Pᵀ = P * (Q * Pᵀ) := by rw [← mul_assoc, hQ, one_mul]
      _ = s • P := by rw [← hs, scalar_apply, ← smul_eq_mul_diagonal]
  have h2 : P = (s * s) • P := by
    have := congrArg transpose h1
    rwa [transpose_transpose, transpose_smul, h1, smul_smul] at this
  have h3 : s * s = 1 := by
    have h4 : (1 : Matrix (Fin n) (Fin n) K) = (s * s) • 1 := by
      calc (1 : Matrix (Fin n) (Fin n) K) = P * Q := hQ.symm
        _ = ((s * s) • P) * Q := by rw [← h2]
        _ = (s * s) • 1 := by rw [smul_mul_assoc, hQ]
    have h5 := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h5.symm
  rcases mul_self_eq_one_iff.1 h3 with rfl | rfl
  · exact Or.inl (by rw [h1, one_smul])
  · exact Or.inr (by rw [h1, neg_smul, one_smul])

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.sign :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P := by
  intro l _ n F c ρ P hsp hf
  have hQ : (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv P
  refine sg_end _ _ hQ fun Z => ?_
  have hZ : Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    have h1 := hf (F.conj g)
    rw [sg_conj_conj, sg_eps_conj] at h1
    exact sg_comm _ _ _ _ _ (ρ (F.conj g)).isUnit P.isUnit hQ h1 (hf g)
  | zero => rw [zero_mul, mul_zero]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SpanOGen
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem spanO_gen {O K : Type} [CommRing O] [Field K] (f : O →+* K) {n : ℕ} (ι : Type)
    (r : ι → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span K (Set.range fun i => (r i).map f) = ⊤) :
    ∃ a : O, a ≠ 0 ∧ ∀ Z : Matrix (Fin n) (Fin n) O, a • Z ∈ Submodule.span O (Set.range r) := by
  classical
  obtain ⟨κ, g, -, hsp, hli⟩ := exists_linearIndependent' K (fun i => (r i).map f)
  rw [h] at hsp
  let b := Module.Basis.mk hli hsp.ge
  haveI : Finite κ := Module.Finite.finite_basis b
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin n × Fin n) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_matrix]
    simp
  let e : Fin n × Fin n ≃ κ := Fintype.equivOfCardEq hcard
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) O := fun p q => r (g (e q)) p.1 p.2
  have hM : f M.det ≠ 0 := by
    rw [RingHom.map_det]
    have hli2 : LinearIndependent K (f.mapMatrix M).col := by
      have hl := (hli.comp e e.injective).map' (LinearEquiv.curry K K (Fin n) (Fin n)).symm.toLinearMap (LinearEquiv.ker _)
      have heq : (f.mapMatrix M).col = (LinearEquiv.curry K K (Fin n) (Fin n)).symm.toLinearMap ∘ ((fun i => (r i).map f) ∘ g) ∘ e := by
        funext q p
        rfl
      rw [heq]
      exact hl
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli2)).ne_zero
  refine ⟨M.det, fun h0 => hM (by rw [h0, map_zero]), fun Z => ?_⟩
  let v : Fin n × Fin n → O := fun p => Z p.1 p.2
  let w := M.adjugate *ᵥ v
  have hw : M *ᵥ w = M.det • v := by
    simp only [w, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
    first
      | simp [Matrix.smul_mulVec]
      | (ext p; simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply])
  have hZ : M.det • Z = ∑ q, w q • r (g (e q)) := by
    ext i j
    have hij := congrFun hw (i, j)
    simp only [Matrix.mulVec, dotProduct, M, v, Pi.smul_apply, smul_eq_mul] at hij
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← hij]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hZ]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem UpperTheory.V.Th.Nm.spanO :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (c : Coef l) (ι : Type) (r : ι → Matrix (Fin n) (Fin n) c.O), Submodule.span (Qbar l) (Set.range fun i => (r i).map (algebraMap c.O (Qbar l))) = ⊤ → ∃ a : c.O, a ≠ 0 ∧ ∀ Z : Matrix (Fin n) (Fin n) c.O, a • Z ∈ Submodule.span c.O (Set.range r) := by
  intro l _ n c ι r h
  exact spanO_gen (algebraMap c.O (Qbar l)) ι r h
end

