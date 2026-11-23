module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0009
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0013
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0008
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLinkB
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVol
section
namespace SheetDecomposition

theorem famVol : FamVol := famVol_of moebVol (stdModel_of stdZ) arithIdx levelDict

theorem ballVolEq : BallVolEq := ballVolEq_of famVol

end SheetDecomposition
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLink
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (s : CMType H ⊕ CMType H)
    (m : Fin (labelRk D s)) : ∃ ρ : CMType H × Fin (D.p + D.q), HodgeCpt.rootIdx D ρ = ⟨s, m⟩ ∧
      HodgeCpt.rootSgn D ρ * HodgeCpt.rootSgn D ρ = 1 ∧
      ∀ (K : Type) (x : CMType H × Fin (D.p + D.q) → K → ℤ), grDeg x s m = HodgeCpt.rootSgn D ρ • x ρ := by
  rcases s with τ | τ
  · have hm : (m : ℕ) < D.p := m.2
    refine ⟨(τ, ⟨m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, hm, dif_pos]
    · simp [HodgeCpt.rootSgn, hm]
    · simp [HodgeCpt.rootSgn, hm, grDeg]
  · have hm : (m : ℕ) < D.q := m.2
    have h : ¬ D.p + D.q - 1 - m < D.p := by omega
    refine ⟨(τ, ⟨D.p + D.q - 1 - m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, h, dif_neg, not_false_eq_true]
      congr 1
      exact Fin.ext (by show D.p + D.q - 1 - (D.p + D.q - 1 - m) = m; omega)
    · simp [HodgeCpt.rootSgn, h]
    · simp [HodgeCpt.rootSgn, h, grDeg]

theorem val_tens {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) {ξ : Sp Ω ⟶ X}
    (q : Cpt ξ) (hR : ∀ a ∈ regAt ξ q, i a ∈ O) (Λ : Lat ξ Ω) {t M : Ω} (ε : ℤ) (ht : Λ.IsGenAt q t)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {M}) :
    O.valuation (i M) = O.valuation (i t) ^ ε := by
  refine le_antisymm (val_le_of_mem_span O i _ hR (S := {t | ∃ s : Unit → Ω, (∀ j, Λ.IsGenAt q (s j)) ∧ t = ∏ j, s j ^ ε}) ?_
    (show M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q from h ▸ Submodule.mem_span_singleton_self M)) ?_
  · rintro _ ⟨s, hs, rfl⟩
    simp [val_eq_of_span_eq O i _ hR ((hs ()).2.symm.trans ht.2)]
  · have : t ^ ε ∈ Submodule.span (regAt ξ q) {M} :=
      h ▸ Submodule.subset_span ⟨fun _ => t, fun _ => ht, by simp⟩
    simpa using val_le_of_mem_span O i _ hR (S := {M}) (γ := O.valuation (i M)) (by rintro _ rfl; rfl) this

theorem val_step {Ω Ω₃ K : Type} [Field Ω] [Field Ω₃] [Fintype K] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (w : K → Ω)
    (x : K → ℤ) {ε : ℤ} (hε : ε * ε = 1) {e t : Ω} (he : e ≠ 0)
    (h : O.valuation (i ((∏ a, w a ^ x a) • e)) = O.valuation (i t) ^ ε) :
    O.valuation (i (∏ a, w a ^ (ε • x) a)) = O.valuation (i t) * O.valuation (i (e ^ ε)⁻¹) := by
  have h3 := congrArg (· ^ ε) h
  simp only [← zpow_mul, hε, zpow_one] at h3
  have h4 : O.valuation (i e) ≠ 0 := by simpa using he
  rw [← h3, smul_eq_mul, map_mul, map_mul, mul_zpow, map_inv₀, map_inv₀, map_zpow₀, map_zpow₀,
    mul_inv_cancel_right₀ (zpow_ne_zero _ h4), ← map_zpow₀, ← map_zpow₀, ← Finset.prod_zpow]
  simp only [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem rootLat_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag)
    (ρ : CMType H × Fin (D.p + D.q)) (s : CMType H ⊕ CMType H) (m : Fin (labelRk D s)) (h : HodgeCpt.rootIdx D ρ = ⟨s, m⟩) :
    Fl.rootLat ρ = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m) fun _ => HodgeCpt.rootSgn D ρ := by
  unfold HodgeCpt.Flag.rootLat
  generalize HodgeCpt.rootIdx D ρ = z at h
  subst h
  rfl

theorem fibLink : ChartVal → Centre → CoordLat → FibLink := by
  intro hCV hC hL E _ _ _ H D l Xo c Y S' Ω' _ K' _ J' _ y' 𝔐 Fl x e b u k _ _ Ω₃ _ _ i hRL hb _ _ hfl hk s m
  classical
  obtain ⟨A, hA, hind, -⟩ := hL E H D l Xo c Y S' Ω' K' J' y' 𝔐 Fl b hb
  have h₀ : LinearIndependent Ω' (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h s
  obtain ⟨β, hβ, hV⟩ := flag_val 𝔐.fn i (fun m => Fl.j (b s m)) (Fl.b s) (u s) (hind s).1 h₀ (hfl s)
  choose ρ hρ hε hx using exists_root D s
  refine ⟨i ((∏ m' ∈ Finset.Iic m, β m') * ∏ m' ∈ Finset.Iic m, (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹),
    (map_ne_zero i).2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m')
      (Finset.prod_ne_zero_iff.2 fun m' _ => inv_ne_zero (zpow_ne_zero _ (hRL _).1))), fun O hO => ?_⟩
  obtain ⟨q, -, hq, -, -⟩ := hC E H D l Xo c Y S' S' Ω' Ω' Ω₃ K' K' J' J' y' y' 𝔐 𝔐 i i O rfl
  have hch : ∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q := fun p hp hn => by
    have : CharZero Ω₃ := charZero_of_injective_algebraMap (algebraMap k Ω₃).injective
    have : CharZero Ω' := i.charZero
    have h0 : (p : Ω') ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine hn ⟨h0, natCast_mem _ _, hq.2 _ (natCast_mem _ _) h0 ?_⟩
    simpa using hO (p : k)⁻¹
  obtain ⟨ch, hc⟩ := 𝔐.tie.cover q
  have hy : ∀ a, y' ⟨a, ch a⟩ ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 hc.1 a (Finset.mem_univ a)
  obtain ⟨U, hU, bb, hbf, hbq⟩ := Fl.sub s q trivial
  obtain ⟨hbi, hbs⟩ := hbq q trivial hU
  obtain ⟨t, ht, hv⟩ := hV O (regAt 𝔐.ξ q) (A s (𝔐.f q.1)) bb hq.1 (fun a => by
    obtain ⟨z, hz⟩ := hk a
    exact hz ▸ hO z) hbi hbf (hbs.symm.trans (hA q hch s))
  have hgen : ∀ m', ((𝔐.V s).gr (Fl.b s) m').IsGenAt q (t m') := fun m' => by
    have := gr_span h₀ hbi hbf (regAt 𝔐.ξ q) m' (ht m')
    rw [← hbs] at this
    exact this
  have hstep : ∀ m', O.valuation (i (∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a)) =
      O.valuation (i (t m')) * O.valuation (i (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹) := fun m' => by
    have h1 := (hRL (ρ m')).2 q trivial ch hc
    have h2 : Fl.rootLat (ρ m') = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m') fun _ => HodgeCpt.rootSgn D (ρ m') :=
      rootLat_eq Fl (ρ m') s m' (hρ m')
    rw [h2] at h1
    rw [hx]
    exact val_step O i _ _ (hε m') (hRL _).1 (val_tens O i q hq.1 _ _ (hgen m') h1)
  have hm : (∏ a, y' ⟨a, ch a⟩ ^ stepDeg x s m a) = ∏ m' ∈ Finset.Iic m, ∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [stepDeg, Finset.sum_apply]
    induction Finset.Iic m using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ (hy a), ih]
  have hpl : vdeg O (plPt fun s => (u s).map i) (plDeg ⟨s, m⟩) = (Finset.univ.sup fun I : Fin (m + 1) → Fin (labelRk D s) =>
      O.valuation (Matrix.of fun a b : Fin (m + 1) => (u s).map i (I a) (Fin.castLE m.2 b)).det)⁻¹ := by
    rw [vdeg, Finset.prod_eq_single (⟨s, m⟩ : Σ s, Fin (labelRk D s)) (fun z _ hz => by simp [plDeg, hz]) (by simp)]
    simp only [plDeg, if_pos, zpow_neg, zpow_one]
    rfl
  have h5 := hv m
  have h6 : O.valuation (i (∏ m' ∈ Finset.Iic m, β m')) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m'))
  rw [hCV _ _ _ O i 𝔐.ξ q K' J' y' ch _ hq hc, hm, hpl, map_mul, map_mul, ← h5, mul_right_comm,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul (h5 ▸ h6)), map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m' _ => hstep m'

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
section
noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum pointConeMap)
open GlobalTheory.CompanionTheory.Ar

namespace PF

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

def cst (ι : K → Type) [∀ b, Fintype (ι b)] : HermLine ι := HermLine.ofWeight (fun _ => 1) fun _ _ _ => rfl

theorem cst_smooth : IsSmoothHerm (cst ι) := contDiffOn_const

theorem ii_cst (hI : PB.Inputs) {II : IntersectionSystem} (hII : IsIntersectionSystem II) {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {y : (Σ b, ι b) → Ω} {e : ℕ} (ha : IsArithVar (mCoordIdeal y) (e + 1)) (a : Fin e → K → ℤ) :
    II K ι (mCoordIdeal y) (e + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun j => fsHerm ι (a j)) (cst ι)) = -inum ℚ y a := by
  classical
  have hs : ∀ j, IsSmoothHerm (fsHerm ι (a j)) := fun j => FsInvPow.isSmoothHerm_fsHerm _
  have h1 := (hII K ι).2.2 _ e (fun j => fsHerm ι (a j)) (cst ι) 1 (fun _ => 0) ha hs cst_smooth (fun _ => rfl)
    Geo.isMultiHomog_one ((Ideal.ne_top_iff_one _).1 ha.2.1.1.ne_top)
  have h3 : logNorm (cst ι) 1 = fun _ => 1 := by
    funext z
    simp [logNorm, cst, HermLine.ofWeight]
  have h2 := Giv.degreeGeneric_of_degree hI.2.1.2.1 K ι _ e (fun j => fsHerm ι (a j)) ha hs
  refine h1.trans ?_
  rw [recR, Geo.divSupp_one, finsum_mem_empty, zero_sub, arInt, h3, inum, pointIdeal_rat]
  exact congrArg _ h2

theorem ii_cast {II : IntersectionSystem} (hII : IsIntersectionSystem II) {P : Ideal (MRing ι)} {d d' : ℕ} (σ : Fin d ≃ Fin d')
    (hP : IsArithVar P d') (L : Fin d' → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) : II K ι P d (L ∘ σ) = II K ι P d' L := by
  obtain rfl : d = d' := Fin.equiv_iff_eq.1 ⟨σ⟩
  exact (hII K ι).1 P d L σ hP hL

theorem pull_inl (a : K → ℤ) : AI.I1.pullDeg (Sum.inl : K → K ⊕ K') a = Sum.elim a 0 := by
  funext k
  rcases k with k | k
  · exact Sum.inl_injective.extend_apply _ _ k
  · exact Function.extend_apply' _ _ _ (by simp)

theorem pull_fs (a : K → ℤ) : IsPullHerm Sum.inl inlV (fsHerm ι a) (fsHerm (Sum.elim ι ι') (Sum.elim a 0)) := by
  refine ⟨(pull_inl a).symm, fun z => ?_⟩
  simp only [fsHerm_h, refNorm, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
  simp
  rfl

theorem pull_cst : IsPullHerm Sum.inl inlV (cst ι) (cst (Sum.elim ι ι')) := by
  refine ⟨?_, fun z => rfl⟩
  show (0 : K ⊕ K' → ℤ) = AI.I1.pullDeg Sum.inl 0
  rw [pull_inl]
  funext k
  rcases k with k | k <;> rfl

def factorAction (n r : ℕ) : Fin (n + 1 + r) ≃ Fin (n + r + 1) where
  toFun j := ⟨if (j : ℕ) < n then j else if (j : ℕ) = n then n + r else j - 1, by have := j.2; split_ifs <;> omega⟩
  invFun j := ⟨if (j : ℕ) < n then j else if (j : ℕ) = n + r then n else j + 1, by have := j.2; split_ifs <;> omega⟩
  left_inv j := by
    have := j.2
    ext
    dsimp only
    split_ifs <;> omega
  right_inv j := by
    have := j.2
    ext
    dsimp only
    split_ifs <;> omega

theorem position_eq {α : Type} {n r : ℕ} (A : Fin n → α) (c : α) (B : Fin r → α) :
    Fin.snoc (α := fun _ => α) (Fin.append A B) c ∘ factorAction n r = Fin.append (Fin.snoc (α := fun _ => α) A c) B := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · have : factorAction n r (Fin.castAdd r (Fin.last n)) = Fin.last _ := by simp [factorAction, Fin.ext_iff]
      simp [this]
    · have : factorAction n r (Fin.castAdd r j.castSucc) = (Fin.castAdd r j).castSucc := by simp [factorAction, Fin.ext_iff]
      simp [this]
  · have : factorAction n r (Fin.natAdd (n + 1) j) = (Fin.natAdd n j).castSucc := by
      have h1 : ¬ n + 1 + j < n := by omega
      have h2 : ¬ n + 1 + j = n := by omega
      simp only [factorAction, Equiv.coe_fn_mk, Fin.val_natAdd, h1, h2, ite_false, Fin.ext_iff, Fin.val_castSucc]
      omega
    rw [Function.comp_apply, this, Fin.snoc_castSucc, Fin.append_right, Fin.append_right]

end PF

open PF in
theorem geoPF : PtDim → GeoPF := by
  intro _ hI II hII Ω₁ _ _ Ω _ _ _ K _ ι _ K' _ ι' _ y y' n r a N hb ha hy'
  classical
  have hne := ne_of_arith ha
  have hP := isPt_join hb ha hy'
  refine ⟨hP, ?_⟩
  have : Nonempty K := ha.1
  have hA := arith_of_isPt hP
  have hgen : ∃ G : GenFibre inlV (mCoordIdeal (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')), ∀ (r : ℕ) (N : Fin r → K' → ℤ),
      intNum G.Φ (fibreIdeal Sum.inl G) (fun j => fibreDeg Sum.inl (Sum.elim (0 : K → ℤ) (N j))) = inum Ω₁ y' N := by
    let B := MvPolynomial K' Ω
    let Φ := FractionRing (MvPolynomial K Ω₁)
    let Φ' := FractionRing (MvPolynomial K B)
    let ν : MvPolynomial K B →+* Φ' := algebraMap _ _
    have hν : Function.Injective ν := IsFractionRing.injective _ _
    let e := sumRingEquiv Ω K K'
    let ν' : MvPolynomial (K ⊕ K') Ω →+* Φ' := ν.comp e.toRingHom
    have hν' : Function.Injective ν' := hν.comp e.injective
    have hg : Function.Injective (ν.comp (MvPolynomial.map (algebraMap Ω₁ B))) :=
      hν.comp (MvPolynomial.map_injective _ (algebraMap Ω₁ B).injective)
    let L : Φ →+* Φ' := IsFractionRing.lift hg
    letI alg : Algebra Φ Φ' := L.toAlgebra
    haveI : ∀ b, Fintype (Sum.elim ι ι' b) := fun b => by
      cases b <;> dsimp <;> infer_instance
    have he : ∀ (c : Ω) (q : Σ b, Sum.elim ι ι' b), e (C c * X q.1) =
        match q with
        | ⟨Sum.inl k, _⟩ => C (C c) * X k
        | ⟨Sum.inr k, _⟩ => C (C c * X k) := by
      rintro c ⟨(k | k), i⟩ <;> simp [e, sumRingEquiv_C, sumRingEquiv_X_inl, sumRingEquiv_X_inr]
    let ψ := pointConeMap Ω₁ y'
    have ha : ∀ c : Ω₁, algebraMap Ω₁ Φ c = algebraMap (MvPolynomial K Ω₁) Φ (C c) := by
      intro c
      rw [IsScalarTower.algebraMap_apply Ω₁ (MvPolynomial K Ω₁) Φ, MvPolynomial.algebraMap_eq]
    have hL : ∀ r, L (algebraMap (MvPolynomial K Ω₁) Φ r) = ν (MvPolynomial.map (algebraMap Ω₁ B) r) := by
      intro r
      exact IsFractionRing.lift_algebraMap hg r
    have hbc := ker_baseChange (algebraMap Ω₁ Φ) ha ν hν L hL ψ
    refine ⟨⟨Φ, Φ', fun p => algebraMap (MvPolynomial K Ω₁) Φ (C (y p) * X p.1),
      fun q => ν' (C (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y' q) * X q.1), ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [image_join]
      exact ker_aeval_cone y (algebraMap (MvPolynomial K Ω₁) Φ) (IsFractionRing.injective _ _)
    · exact gen_cone hb hne
    · exact ker_aeval_cone _ ν' hν'
    · intro p
      rw [RingHom.algebraMap_toAlgebra]
      show ν (e _) = L _
      rw [IsFractionRing.lift_algebraMap, he]
      simp [inlV, joinPt, ν]
      rfl
    · intro r N
      have hdeg : (fun j => fibreDeg Sum.inl (Sum.elim (0 : K → ℤ) (N j))) = fun j => N j ∘ (blkE K K').symm := by
        funext j b
        obtain ⟨(k | k), h⟩ := b
        · exact absurd ⟨k, rfl⟩ h
        · rfl
      rw [hdeg]
      dsimp only
      rw [← FieldNumbers.RenameIntNum.full Φ K' (FibreBlock (Sum.inl : K → K ⊕ K')) ι'
        (fibreIdx (Sum.elim ι ι') Sum.inl) (blkE K K') (varE ι ι') (fun v => rfl)]
      have hmap : ∀ P : Ideal (NumbersDVR.MRing ι' Ω₁),
          intNum Φ (Ideal.map (MvPolynomial.map (algebraMap Ω₁ Φ)) P) N = intNum Ω₁ P N := by
        intro P
        unfold intNum
        congr 2
        funext m
        exact FieldNumbers.hilbFn_map P m
      refine Eq.trans ?_ (hmap (RingHom.ker ψ))
      rw [← hbc]
      congr 1
      ext f
      simp only [Ideal.mem_comap, fibreIdeal, RingHom.mem_ker, MvPolynomial.aeval_rename]
      rw [MvPolynomial.aeval_eq_eval₂Hom]
      congr! 3
      funext s
      obtain ⟨k, i⟩ := s
      have h1 := he (y' ⟨k, i⟩) ⟨Sum.inr k, i⟩
      simp only [Function.comp_apply, varE, Equiv.coe_fn_mk, ν', RingHom.comp_apply, joinPt]
      show ν (e (C (y' ⟨k, i⟩) * X (Sum.inr k))) = _
      rw [h1]
      simp [ψ, pointConeMap]
  obtain ⟨G, hG⟩ := hgen
  have hsm : ∀ {m : ℕ} {α : Type} [Fintype α] {κ : α → Type} [∀ b, Fintype (κ b)] (b : Fin m → α → ℤ) (j : Fin (m + 1)),
      IsSmoothHerm (Fin.snoc (α := fun _ => HermLine κ) (fun j => fsHerm κ (b j)) (cst κ) j) := by
    intro m α _ κ _ b j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using cst_smooth
    · simpa using FsInvPow.isSmoothHerm_fsHerm _
  have h := hI.2.2.2.1.1 II hII.1 K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl inlV _ (n + 1) r G (fun V _ L => intNum G.Φ V L)
    (Fin.snoc (α := fun _ => HermLine ι) (fun j => fsHerm ι (a j)) (cst ι))
    (Fin.snoc (α := fun _ => HermLine (Sum.elim ι ι')) (fun j => fsHerm (Sum.elim ι ι') (Sum.elim (a j) 0)) (cst _))
    (fun j => fsHerm (Sum.elim ι ι') (Sum.elim 0 (N j))) isBlockMap_inl (by rwa [Nat.add_right_comm])
    (by rwa [image_join]) (NumbersDVR.IntNumIsFieldIntersection.full _ _ _) (hsm a)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using pull_cst
      · simpa using pull_fs _)
    fun j => FsInvPow.isSmoothHerm_fsHerm _
  rw [image_join, ii_cst hI hII.1 ha, ← position_eq] at h
  have e : (Fin.append (fun j => fsHerm (Sum.elim ι ι') (Sum.elim (a j) 0)) fun j => fsHerm (Sum.elim ι ι') (Sum.elim 0 (N j))) =
      fun j => fsHerm (Sum.elim ι ι')
        (Fin.append (fun j => Sum.elim (a j) (0 : K' → ℤ)) (fun j => Sum.elim (0 : K → ℤ) (N j)) j) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  rw [e, ii_cast hII.1 _ hA _ (hsm _), ii_cst hI hII.1 hA] at h
  have h' := hG r N
  rw [mul_neg, neg_inj] at h
  rw [num, num, finrank_join y' hb hne, mul_assoc, ← h']
  congr 1
  exact_mod_cast h

end SheetDecomposition
end
end

