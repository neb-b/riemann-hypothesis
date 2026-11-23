module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.NotDvdIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.SpDims
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AbsPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.MemMaxIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IncLoc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_bot {S k : Type} [TopologicalSpace S] [CommRing k] {x : S → k} (h : AdicCont ⊥ x) : IsLocallyConstant x :=
  IsLocallyConstant.desc _ _ (h 1) ((Ideal.Quotient.mk_bijective_iff_eq_bot _).2 (pow_one _)).1

private theorem fin_res {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  obtain ⟨-, -, h1, -⟩ := dvrFacts l c.O
  haveI := h1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem inc_loc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, ((residue c'.O).comp (inc h)) x = 0 := by
  have hi : (inc h).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) (inc h) ?_
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := (Subalgebra.inclusion h).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral x
  haveI := hi.isLocalHom (Subalgebra.inclusion_injective h)
  intro x hx
  exact (residue_eq_zero_iff _).2 (map_nonunit (inc h) x hx)

private theorem count {O Γ Γb : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb]
    (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ) (hstd : Φ.Std l a)
    (π : Γ →* Γb) (hQ : Φ.Quo π) (s : PD Φ.ι Γ (ResidueField Λ)) (hs : Φ.IsRes ((residue Λ).comp a) s)
    (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) (hP : Φ.IsDef a s P)
    (tN : ∀ g ∈ Φ.N, Φ.ν g = 1) (tM : ∀ v, ∀ g ∈ Φ.Mu v, Φ.ν g = 1) (ζ : Φ.ι → Γ) (hζ : ∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v))
    (CC : Γ → Prop) (tC : ∀ g, CC g → g * g = 1 ∧ Φ.ν g = -1) (ω : Γ → ResidueField Λ)
    (tW : ∀ w, ∃ g, ((residue Λ).comp a) (Φ.rt w g) ≠ ω g) (d : ℕ)
    (ec : ∀ (ρ : Representation (ResidueField Λ) Γb (sp4 (ResidueField Λ))) (b : Φ.ι → Submodule (ResidueField Λ) (sp4 (ResidueField Λ))),
      IsOpen (ρ.ker : Set Γb) → (∀ v, ∀ g ∈ Φ.Gv v, ∀ X ∈ b v, ρ (π g) X ∈ b v) →
      (∀ f : sp4 (ResidueField Λ) →ₗ[ResidueField Λ] ResidueField Λ, (∀ g X, f (ρ (π g) X) = ω g * f X) → f = 0) →
      (∀ v, Module.finrank (ResidueField Λ) (b v) = 6) →
      (∀ g, CC g → Module.finrank (ResidueField Λ) (LinearMap.ker (ρ (π g) - 1)) ≤ 4) →
      Module.Finite (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) ∧
      Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 ρ b) + d * 6 ≤
        Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) ρ b) + d * 4) :
    ∃ m n : ℕ, HasPres Λ R m n ∧ n + 2 + 2 * d ≤ m + 2 * Nat.card Φ.ι := by
  have h2 : (2 : ResidueField Λ) ≠ 0 := hstd.ok.two.ne_zero
  obtain ⟨hstd', hs', R', _, _, _, P', hP'⟩ := X1.defEx Φ l a hstd s hs
  have hQ' : Φ.noMu.Quo π := ⟨hQ.cont, hQ.onto, hQ.ker⟩
  obtain ⟨rb, hrb, hrc⟩ := (X1.descend Φ π hQ (⊥ : Ideal (ResidueField Λ))).1 s.r hs.pair.kill hs.cont
  have hrb' : ∀ g, rb (π g) = s.r g := fun g => DFunLike.congr_fun hrb g
  have hb0 : ∀ g, ∃ x, IsGSp x (s.r g) := fun g => ⟨_, hs.pair.mult g⟩
  have hb : ∀ g, ∃ x, IsGSp x (rb g) := fun g => by
    obtain ⟨g, rfl⟩ := hQ.onto g
    rw [hrb']; exact hb0 g
  have had : ∀ g X, adSp rb hb (π g) X = adSp s.r hb0 g X := fun g X => Subtype.ext (by
    rw [adSp_val, adSp_val, ← map_inv, hrb', hrb'])
  obtain ⟨a1, a2⟩ := X1.adFacts rb hb
  obtain ⟨-, d2⟩ := X1.spDims (ResidueField Λ) h2
  obtain ⟨e1, e2⟩ := ec (adSp rb hb) (fun v => bor (s.n v)) (a1 fun i j => lc_bot (hrc i j)).1
    (fun v g hg X hX => a2 (s.n v) (π g) (hs.pair.low v).1 (by rw [hrb']; exact hs.pair.flag v g hg)
      (by rw [← map_inv, hrb']; exact hs.pair.flag v g⁻¹ (inv_mem hg)) X hX)
    (fun f hf => X1.dualZero Φ _ hstd.ok s hs.res hb0 ω tW f fun g X => by rw [← had]; exact hf g X)
    (fun v => (d2 _ (hs.pair.low v).1).1)
    (fun g hg => X1.ccDim rb hb h2 (π g) (by rw [← map_mul, (tC g hg).1, map_one]) (by
      have h1 := hs.pair.mult g
      rw [(tC g hg).2, Units.val_neg, Units.val_one, map_neg, map_one] at h1
      rw [hrb']
      exact h1))
  obtain ⟨m, p1, p2⟩ := X1.absPres Φ.noMu l a hstd' (fun _ => rfl)
    (fun g hg => by
      have h1 : Φ.noMu.ν g = 1 := tN g hg
      rw [h1, Units.val_one, map_one]) π hQ' s hs' R' P' hP' rb hb hrb e1
  obtain ⟨g, e, g1, g2⟩ := X1.muQuot Φ l a hstd s hs ζ hζ
    (fun v => by rw [tM v (ζ v) (hζ v).1, Units.val_one, map_one]) R P hP R' P' hP'
  refine ⟨_, _, X1.presQuot Λ R' R _ _ _ g e p1 g1 g2, ?_⟩
  have hc : Nat.card (Φ.ι × Fin 2) = 2 * Nat.card Φ.ι := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, mul_comm]
  rw [hc]
  have p3 : Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + 2 ≤
      m + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 (adSp rb hb) fun v : Φ.ι => bor (s.n v)) := p2
  show Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + _ + 2 + 2 * d ≤ _
  omega

theorem UpperTheory.V.Ws.x1 :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (s : PD T.ι (G T.F Ω) (ResidueField c'.O)), (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) s →
      ∀ (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R] (P : PD T.ι (G T.F Ω) R), (T.fr ∅).IsDef (inc h) s P →
      ∃ (a b : ℕ) (π : MvPowerSeries (Fin a) c'.O →ₐ[c'.O] R) (f : Fin b → MvPowerSeries (Fin a) c'.O), Function.Surjective π ∧
        RingHom.ker π = Ideal.span (Set.range f) ∧ b + 2 + 2 * T.d ≤ a + 2 * Nat.card T.ι := by
  intro hp Ω _ _ _ l _ c D T hF hD c' h s hs R _ _ _ P hP
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := inferInstance
  haveI := fin_res c'
  have hstd := (UpperTheory.V.Ws.std hp D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  haveI := hstd.char
  obtain ⟨tN, tM, tC, tW⟩ := X1.thFacts D T hF hD
  obtain ⟨S, K, Γ, _, _, _, _, _, _, π, ι, hG, hS, hpl, hQ⟩ := X1.linkT D T hF
  have hpr : UpperTheory.V.GC.Hypotheses₂ := ⟨⟨hp.loc.lf, hp.loc.lt, hp.loc.le, hp.gf, hp.ge, hp.pt⟩, hp.uo, hp.gw⟩
  choose ζ hζ using fun v : T.ι => X1.muLoc hp T.F Ω l (T.pl v) (T.ovl v)
  have ec := fun ρ b => X1.ecG hpr T.F Ω l T.realF S K Γ π hG hS T.ι ι T.pl hpl (ResidueField c'.O) (sp4 (ResidueField c'.O)) ρ b 6 4
  have tW' := tW (ResidueField c'.O) ((residue c'.O).comp (inc h)) (inc_loc h)
  have key := count (T.fr ∅) l (inc h) hstd π hQ s hs R P hP tN tM ζ hζ IsCC tC
    (fun g => (UpperTheory.V.GC.cycF T.F Ω l (ResidueField c'.O) g : ResidueField c'.O)) tW' T.d
  obtain ⟨m, n, ⟨π', f, q1, q2⟩, q3⟩ := key ec
  exact ⟨m, n, π', f, q1, q2, q3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NotOver
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem not_over {Ω : Type} [Field Ω] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : q ≠ p) {A : ValuationSubring Ω}
    (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := fun hq' => by
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 e)
  have h1 : A.valuation ((a : Ω) * (q : Ω) + (b : Ω) * (p : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hq'
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A b))) hA
  have h2 : (a : Ω) * (q : Ω) + (b : Ω) * (p : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

section
variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

private theorem uM_map {Y : M4 R} (h : Y ∈ uM R) : Y.map f ∈ uM R' := by
  refine ⟨fun i j e => by rw [Matrix.map_apply, h.1 i j e, map_zero], ?_⟩
  have e : adj Y = -Y := h.2
  show adj _ = -_
  rw [(grp R).2.2.2.2.2.1, e]
  ext i j
  simp

private theorem blk_map {Y : M4 R} (h : IsBlock Y) : IsBlock (Y.map f) := fun i j e => by
  rw [Matrix.map_apply, h i j e, map_zero]

private theorem rep_eq {Γ : Type} [Group Γ] (r : Γ →* M4 R) (g : Γ) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem adj_map (Y : M4 R) : adj (f.mapMatrix Y) = f.mapMatrix (adj Y) := (grp R).2.2.2.2.2.1 R' f Y

private theorem eAB_map : (eAB R).map f = eAB R' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eAB]

end

theorem UpperTheory.V.Ws.bl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      Submodule.span 𝔞.K (Set.range fun g => (mapRep 𝔞.toK r g).submatrix ixA ixA) = ⊤ →
      ∃ r' u', KPair D 𝔞 r' u' ∧ BlockExt (mapRep 𝔞.toK r') ∧ ∀ g, (r' g).charpoly = (r g).charpoly := by
  intro hP Ω _ _ _ l hl c D hD 𝔞 r u hK hB hsp
  obtain ⟨hpos, h2, A, _, _, _, f, r₁, u₁, hf, hr, hu, hlA, hb⟩ := toGlobalTheory D hD 𝔞 r u hK hB
  haveI := hf.fin
  haveI := hf.loc
  obtain ⟨r', z, y, e, hc, hz, hy, hm, hzc, hN, hfl, hne⟩ := cocA hP _ _ _ _ hpos A r₁ u₁ hf.complete hlA hb
  have hinj : Function.Injective (f.mapMatrix : M4 A →+* M4 𝔞.V) := Matrix.map_injective hf.inj
  have er : ∀ g, r g = f.mapMatrix (r₁ g) := fun g => by rw [← hr]; rfl
  have eu : u = f.mapMatrix u₁ := hu.symm
  have eV : ∀ g, mapRep f r' g = (1 + (z g).map f) * r g := fun g => by
    rw [rep_eq, e, map_mul, map_add (f := _), map_one, er]; rfl
  have hzV : ∀ g, (z g).map f ∈ uM 𝔞.V := fun g => uM_map f (hz g)
  have hyV := uM_map f hy
  have kill : ∀ g (B : ValuationSubring Ω), ¬ B.valuation (l : Ω) < 1 → g ∈ Ine (F := ℚ) B → r g = 1 → mapRep f r' g = 1 :=
    fun g B h1 h3 h4 => by
      have h5 : r₁ g = 1 := hinj (by rw [← er, h4, map_one])
      rw [eV, hN g ⟨h5, B, h1, h3⟩, h4]
      simp
  have fl : ∀ s ∈ D.Gp l, IsUp (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u)) ∧
      ∀ i, (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u) : M4 𝔞.V) i i = (adj u * r s * u : M4 𝔞.V) i i :=
    fun s hs => by
      rw [eV]
      refine twistFlag _ (r s) (r s⁻¹) _ _ u (hB s) (hB _) (by rw [← map_mul, inv_mul_cancel, map_one]) (hzV s) hyV hK.sp
        (hK.flag s hs) fun i j hij => ?_
      have h1 : adj u * ((z s).map f - (r s * y.map f * r s⁻¹ - y.map f)) * u =
          f.mapMatrix (adj u₁ * (z s - (r₁ s * y * r₁ s⁻¹ - y)) * u₁) := by
        rw [eu, er, er, adj_map]
        simp only [map_mul, map_sub]
        rfl
      rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, hfl s hs i j hij, map_zero]
  have eK : ∀ g, mapRep 𝔞.toK (mapRep f r') g = (1 + ((z g).map f).map 𝔞.toK) * mapRep 𝔞.toK r g := fun g => by
    rw [rep_eq, eV, map_mul, map_add (f := _), map_one]; rfl
  have hBK : ∀ g, IsBlock (mapRep 𝔞.toK r g) := fun g => blk_map 𝔞.toK (hB g)
  have hzK : ∀ g, ((z g).map f).map 𝔞.toK ∈ uM 𝔞.K := fun g => uM_map _ (hzV g)
  refine ⟨mapRep f r', (1 - y.map f) * u, ⟨⟨A, _, _, _, f, ⟨r', fun _ => (1 - y) * u₁⟩, hf, hc, ?_⟩, fun g i j => ?_, fun g => ?_,
    fun B hA g hg h1 => ?_, fun p hp g hg => ?_, ?_, fun s hs => (fl s hs).1, fun s hs i => ?_, fun s hs i => ?_⟩,
    ⟨fun g i j h => ?_, ?_, ?_⟩, fun g => ?_⟩
  · refine PD.ext rfl (funext fun _ => ?_)
    show f.mapMatrix ((1 - y) * u₁) = _
    rw [map_mul, map_sub, map_one, eu]; rfl
  · rw [eV, add_mul, one_mul, Matrix.add_apply, add_sub_right_comm]
    refine Ideal.add_mem _ (hK.red g i j) ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (map_nonunit f _ (hm g i k))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).1 _ _ (hK.mult g)
  · exact kill g B (hA l (Finset.mem_insert_self _ _)) hg (hK.unr B hA g hg h1)
  · obtain ⟨h3, h4, -⟩ := (facts D hD).1 p hp
    exact kill g _ (not_over h3 hl.out h4.symm (hD.pl_over p h3)) hg.1 (hK.atP p hp g hg)
  · rw [sub_eq_add_neg]
    exact (twistPt _ _ _ (hB 1) (neg_mem hyV)).1 _ _ hK.sp
  · rw [(fl s hs).2]
    exact hK.char s hs i
  · rw [(fl s (Ine_le_Dec _ hs)).2]
    exact hK.inert s hs i
  · rw [eK]
    exact (twistPt _ _ _ (hBK g) (hzK g)).2.1 i j h
  · rw [show (fun g => (mapRep 𝔞.toK (mapRep f r') g).submatrix ixB ixB) = fun g => (mapRep 𝔞.toK r g).submatrix ixB ixB from
      funext fun g => by rw [eK]; exact (twistPt _ _ _ (hBK g) (hzK g)).2.2.1]
    refine spanB _ _ _ ⟨fun g => ⟨𝔞.toK (𝔞.a c (D.th g)), ?_⟩, hBK⟩ hsp
    have h1 := congrArg (𝔞.toK.mapMatrix : M4 𝔞.V →+* M4 𝔞.K) (hK.mult g)
    rw [map_mul, ← adj_map] at h1
    refine h1.trans ?_
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rintro ⟨Y, hY, hblk⟩
    have h3 : IsUnit (2 : 𝔞.K) := by have := h2.map 𝔞.toK; rwa [map_ofNat] at this
    have h4 := noCompl _ _ (mapRep 𝔞.toK r) (fun g => ((z g).map f).map 𝔞.toK) D.cc Y h3 hBK (fun g => (hzK g).1)
      (by rw [rep_eq, er, hb.cc]; exact (congrArg (·.map 𝔞.toK) (eAB_map f)).trans (eAB_map _))
      (by rw [hzc]; ext i j; simp) hY fun g => by rw [← eK]; exact hblk g
    refine hne (funext fun g => ?_)
    ext i j
    exact hf.inj (Subtype.ext (by simpa using congrFun (congrFun (h4 g) i) j))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).2.2.2
end

