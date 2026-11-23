module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiesEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsResidualRepRestrictionOfLatticeShape
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.ExistsResidualDatumOverRestrictionToRationals
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Chain3
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

open UpperTheory.V.Ws.Chn in
theorem UpperTheory.V.Ws.chain3 :
    CohomologyHyp → SeedIII → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → T₀.Three → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hC hS Ω _ _ _ l _ c D T₀ h3 hok hth htame ι 𝔞 c₀ hc₀
  have hG : D.Good := h3.1
  have hF : T₀.Fit := ⟨hok, Or.inr ⟨h3, hth.five, hth.sb, hth.psi⟩⟩
  have ha := red_zero 𝔞 c
  have ok0 : (T₀.fr ∅).Ok (𝔞.red c) := (std hC D T₀ hF ∅ c le_rfl).2 _ _ ha
  obtain ⟨w, s, hw, hsp, hs, hsM, hsA, hsB, hseed⟩ := hS Ω l c D T₀ h3 hok hth ι 𝔞
  obtain ⟨p0, hp0, hov0⟩ := UpperTheory.exists_residualRep_restriction_of_latticeShape D hG T₀ hF _ _ ha ok0 c₀ hc₀
  obtain ⟨-, hp0P, -⟩ := goodQ D hG T₀ hF _ _ ha _ c₀ p0 hc₀ (fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw) hov0 hp0 ∅
  obtain ⟨W1, p2, hW1, hW1s, hp2, hp2Q, hp2A, hp2E⟩ :=
    gysinPs hC D T₀ hF _ _ ha {w} (by simpa using ⟨hw, hsp⟩) s hs hsM
  obtain ⟨W2, p3, p4, hW2, hW2s, hp3, hp4, hp3Q, hp4Q, h30, h42, h34, h3E⟩ :=
    gysinAl hC D T₀ hF _ _ ha W1 hW1s p0 p2 (res_mono T₀ (Finset.empty_subset _) hp0) hp2 hp0P (qP hp2Q)
  obtain ⟨T₁, hL1, ht1, hd1⟩ := diesEx D hG T₀ htame hok W2 hW2s
  refine ⟨T₁, hL1, ht1, fun T hL _ => ?_⟩
  have hT : T₀.Le T := (leFit D hG T₀ T₁ hL1).2.2.2.2.2.2 T hL
  obtain ⟨lo, -, l3, -, lf, -, -⟩ := leFit D hG T₀ T hT
  have hd : ∀ w ∈ W2, Dies l w T.F := fun w hw => dies_mono hL.le (hd1 w hw)
  obtain ⟨c₁, h, Q, hQ, hovs⟩ := hseed T hT (lo hok) (l3 hth) (hd w (hW2 (hW1 (Finset.mem_singleton_self w))))
  refine ⟨c₁, h, Q, hQ, fun u hu hur => ?_⟩
  have okT : (T.fr ∅).Ok (𝔞.red c) := (std hC D T (lf hF) ∅ c le_rfl).2 _ _ ha
  have hq := seed_res T 𝔞 hQ
  replace hs := res_mono T₀ (hW1.trans hW2) hs
  replace hp0 := res_mono T₀ (Finset.empty_subset W2) hp0
  replace hp2 := res_mono T₀ hW2 hp2
  have R := fun x hx => restrT D hG T₀ T hT hF _ _ ha W2 hW2s hd x hx (Or.inl hth.five)
  obtain ⟨q0, hq0, o0⟩ := R p0 hp0
  obtain ⟨q2, hq2, o2⟩ := R p2 hp2
  obtain ⟨q3, hq3, o3⟩ := R p3 hp3
  obtain ⟨q4, hq4, o4⟩ := R p4 hp4
  have O := overFacts D hG T₀ T hT hF _ _ ha W2 ∅
  obtain ⟨-, -, -, a1, -, -, -, a2⟩ := O p0 p3 q0 q3 hp0 hp3 hq0 hq3 o0 o3
  obtain rfl : u = q0 := a2 c₀ _ hc₀.res.pair hov0 u hur hu
  obtain ⟨-, b0, b1, -, b2, -, b4, -⟩ := O p3 p4 q3 q4 hp3 hp4 hq3 hq4 o3 o4
  obtain ⟨-, c0, c1, c2, -, -, -, -⟩ := O p4 p2 q4 q2 hp4 hp2 hq4 hq2 o4 o2
  obtain ⟨-, d0, d1, -, d2, d3, -, -⟩ := O p2 s q2 _ hp2 hs hq2 hq o2 hovs
  obtain ⟨-, e0, -, -, -, -, e4, -⟩ := O s s _ _ hs hs hq hq hovs hovs
  have hlat : LatShape D T.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ := hT.pr ▸ hc₀
  have hrt : ∀ w ∈ roots, 𝔞.red c ((frQ D T.pr (resQ T₀.F T₀.g0)).rt w (resQ T₀.F T₀.g0)) ≠ 1 := by
    rw [hT.pr]; exact fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw
  obtain ⟨-, uP, ug⟩ := goodQ D hG T (lf hF) _ _ ha _ c₀ u hlat hrt hu hur ∅
  have P3 := b1 (qP hp3Q)
  have P4 := c1 (qP hp4Q)
  have P2 := d1 (qP hp2Q)
  have M3 := b0 _ (qM hp3Q.1)
  have M4 := c0 _ (qM hp4Q.1)
  have M2 := d0 _ (qM hp2Q.1)
  have Ms := e0 _ hsM
  have s03 := a1 hp0P (qP hp3Q) (samePs_symm h30)
  have s34 := b2 (qM hp3Q.1) (qM hp4Q.1) h34
  have s42 := c2 (qP hp4Q) (qP hp2Q) h42
  have s2s := d2 (qM hp2Q.1) hsM hp2A
  have A3 := (b4 (qM hp3Q.1)).1 h3E
  have As := (e4 hsM).1 hsA
  have E2 := d3 (qP hp2Q).1 hp2E
  have g0 : (T.fr ∅).Good (𝔞.red c) u :=
    ug.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have g3 : (T.fr ∅).Good (𝔞.red c) q3 :=
    ug.elim (fun x => Or.inl ⟨(samePs_ent hur hq3 uP.1 P3.1 s03).1 x.1, Or.inr A3⟩)
      fun x => Or.inr (Or.inr (Or.inl ⟨samePs_inV hq3 P3 s03 x.1, A3⟩))
  have g4 : (T.fr ∅).Good (𝔞.red c) q4 :=
    Or.inl ⟨(samePs_ent hq4 hq2 P4.1 P2.1 s42).2 E2, Or.inr ((sameAl_ent hq3 hq4 M3 M4 s34).1 A3)⟩
  have g2 : (T.fr ∅).Good (𝔞.red c) q2 := Or.inl ⟨E2, Or.inr ((sameAl_ent hq2 hq M2 Ms s2s).2 As)⟩
  have gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := Or.inr (Or.inl ⟨As, (e4 hsM).2 hsB⟩)
  exact ⟨g0, (((Relation.ReflTransGen.single ⟨g3, lineP _ _ okT _ _ hur hq3 uP P3 s03⟩).tail
    ⟨g4, lineM _ _ okT _ _ hq3 hq4 M3 M4 s34⟩).tail ⟨g2, lineP _ _ okT _ _ hq4 hq2 P4 P2 s42⟩).tail
    ⟨gs, lineM _ _ okT _ _ hq2 hq M2 Ms s2s⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NePure
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def blockChar {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : ∀ g, IsBlock (r g)) (ix : Fin 2 → Fin 4)
    (hix : ix = ixA ∨ ix = ixB) : H →* K where
  toFun g := ((r g).submatrix ix ix).det
  map_one' := by
    rw [map_one, Matrix.submatrix_one ix (by rcases hix with rfl | rfl <;> decide), Matrix.det_one]
  map_mul' a b := by
    rw [← Matrix.det_mul, map_mul]
    congr 1
    have ha := h a
    ext i j
    rcases hix with rfl | rfl
    · have h1 : ∀ i, r a (ixA i) 1 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixA i) 3 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero]
      rfl
    · have h1 : ∀ i, r a (ixB i) 0 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixB i) 2 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero,
        zero_add]
      rfl

theorem UpperTheory.V.Ws.nePure :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      ¬ Pure ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l hl c D hD ι 𝔞 e he r u hp hb ⟨H, M, hH, hM, hP⟩
  obtain ⟨-, f2, -, f4, -⟩ := facts D hD
  obtain ⟨a1, -, a3⟩ := f2 l (Finset.mem_insert_self _ _)
  set φ : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK with hφ
  set ρ := mapRep φ r with hρ
  have hb' : ∀ g, IsBlock (ρ g) := fun g i j h => by rw [hρ, mapRep_apply, hb g i j h, map_zero]
  have hc : Continuous ρ := smallCont 𝔞 e he _ hp.small
  haveI : CharZero 𝔞.V := φ.charZero
  have hu : adj u * u = 1 := by simpa [IsGSp] using hp.sp
  have hdet : ∀ s ∈ D.Ip l, ((r s).submatrix ixA ixA).det = 𝔞.a c (D.ps 0 s) * 𝔞.a c (D.ps 2 s) ∧
      ((r s).submatrix ixB ixB).det = 𝔞.a c (D.ps 1 s) * 𝔞.a c (D.ps 3 s) := fun s hs => by
    have h := blockDet (maximalIdeal 𝔞.V) (fun i => 𝔞.a c (D.ps i (D.sg l))) u (adj u) (r (D.sg l)) (r s) hu
      (fun i j hij hm => a3 i j hij (by
        rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at hm
        exact Ideal.Quotient.eq.2 hm))
      (hb _) (fun i j => by
        have h1 := hp.red (D.sg l) i j
        have h2 : 𝔞.a c (D.r0 (D.sg l) i j) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i (D.sg l))) i j := by
          show 𝔞.a c (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i j) = _
          rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
          split_ifs <;> simp
        rwa [h2] at h1)
      (hp.flag _ a1) (hp.char _ a1) (hb _) (hp.flag s (Ine_le_Dec _ hs))
    simpa only [hp.inert s hs] using h
  have hps : ∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, φ (𝔞.a c (D.ps i s)) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ D.wts4 i := fun i s hs => by
    rw [f4 i s hs, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact congrArg (· ^ _) (he.1 c _)
  have key : ∀ (ix : Fin 2 → Fin 4) (hix : ix = ixA ∨ ix = ixB) (i j : Fin 4),
      (∀ s ∈ D.Ip l, ((r s).submatrix ix ix).det = 𝔞.a c (D.ps i s) * 𝔞.a c (D.ps j s)) →
      ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, ((ρ g).submatrix ix ix).det =
        algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ (D.wts4 i + D.wts4 j) := fun ix hix i j h => by
    have h1 : ∀ g, r g = 1 → blockChar ρ hb' ix hix g = 1 := fun g hg => by
      have : ρ g = ρ 1 := by
        ext i j
        rw [hρ, mapRep_apply, mapRep_apply, hg, map_one r]
      rw [← map_one (blockChar ρ hb' ix hix)]
      exact congrArg (fun X : M4 _ => (X.submatrix ix ix).det) this
    refine wtChar D hD (blockChar ρ hb' ix hix) _ (hc.matrix_submatrix ix ix).matrix_det
      (fun A hA g hg h2 => h1 g (hp.unr A hA g hg h2)) (fun p h2 g hg => h1 g (hp.atP p h2 g hg)) fun s hs => ?_
    rw [pow_add, ← hps i s hs, ← hps j s hs, ← map_mul, ← h s hs.1.1, RingHom.map_det]
    rfl
  obtain ⟨U, hU, hU'⟩ := key ixA (Or.inl rfl) 0 2 fun s hs => (hdet s hs).1
  obtain ⟨W, hW, hW'⟩ := key ixB (Or.inr rfl) 1 3 fun s hs => (hdet s hs).2
  obtain ⟨p, A, f, σ, h1, h2, h3, h4, h5, h6, h7⟩ := frobIn Ω l (H ⊓ (U ⊓ W)) M (hH.inter (hU.inter hW)) hM
  have h8 := pureDet (ι : PadicAlgCl l →+* ℂ) (ρ σ) (hb' σ) (hP p h1 h2 A h3 f σ h4 h5.1 h6)
  rw [hU' σ h5.2.1, hW' σ h5.2.2, h7] at h8
  simp only [map_pow, map_natCast, norm_pow, Complex.norm_natCast] at h8
  have h9 : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ (by exact_mod_cast h1.one_lt) h4.ne'
  have h10 : D.e + 1 + 1 = D.e + 0 := pow_right_injective₀ (zero_lt_one.trans h9) h9.ne' h8
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SuppMono
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)

theorem UpperTheory.V.Ws.chain2 :
    CohomologyHyp → SeedII → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx2 D → T₀.Ok → T₀.Two → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hP hS Ω _ _ _ l _ c D T₀ hC hO hT hL ι 𝔞 c₀ hc₀
  have hG : D.Good := hC.1
  have hF : T₀.Fit := ⟨hO, Or.inl ⟨hC, hT⟩⟩
  have ha : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hrt := (Chain.rtFacts D hG T₀ hO _ _ ha).1
  obtain ⟨s₀, hs₀, ho₀⟩ := Chain.exists_residual_datum_over_restriction_to_rationals hP D T₀ hF _ _ ha c₀ hc₀.res ⟨hc₀.supp, fun _ => hc₀.flag⟩
  have hq₀ := goodQ D hG T₀ hF _ _ ha _ c₀ s₀ hc₀ hrt ho₀ hs₀
  obtain ⟨W, s, -, -, hW, hs, -, hsQ, -, hsP, -, -, hsA⟩ :=
    gysinAl hP D T₀ hF _ _ ha ∅ (by simp) s₀ s₀ hs₀ hs₀ (hq₀ ∅).2.1 (hq₀ ∅).2.1
  obtain ⟨T₁, h01, hL1, hD⟩ := diesEx D hG T₀ hL hO W hW
  refine ⟨T₁, h01, hL1, fun T h1 hdeep => ?_⟩
  have h0 : T₀.Le T := (leFit D hG T₀ T₁ h01).2.2.2.2.2.2 T h1
  obtain ⟨lO, lT, -, -, lF, -⟩ := leFit D hG T₀ T h0
  have tO := lO hO
  have tT := lT hT
  have tF := lF hF
  have hDT : ∀ w ∈ W, Dies l w T.F := fun w hw θ h1' h2 =>
    (IntermediateField.fixingSubgroup_antitone h1.le).trans (hD w hw θ h1' h2)
  obtain ⟨c₁, h, Q, hQ, hQV, hQE⟩ := hS Ω l c D T hC tO tT hdeep ι
  refine ⟨c₁, h, Q, hQ, fun c₀' ho hr => ?_⟩
  obtain ⟨sR, sV, sE⟩ := Chain.seedRes D T ι 𝔞 h Q hQ
  have sV := sV hQV
  obtain ⟨c₃, r₃, o₃⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s hs (Or.inr (Or.inl hsQ.1))
  obtain ⟨t, rt, ot⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s₀ (hq₀ W).1 (Or.inr (Or.inr hs₀))
  have hsP' : s.In nP := ⟨fun g => supp_mono (by decide) (hsQ.1 g), hsQ.2⟩
  have hsM : Supp nM s.r := fun g => supp_mono (by decide) (hsQ.1 g)
  obtain ⟨-, f2, f3, f4, -, -, f7, -⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s s₀ c₃ t hs (hq₀ W).1 r₃ rt o₃ ot
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s₀ s t c₃ (hq₀ W).1 hs rt r₃ ot o₃
  obtain rfl : c₀' = t := g8 c₀ _ hc₀.res.pair ho₀ c₀' hr ho
  have q₃ : Supp qQ c₃.r := f2 _ hsQ.1
  have i₃ : c₃.In nP := f3 hsP'
  have m₃ : Supp nM c₃.r := f2 _ hsM
  have p₃ : c₃.SamePs c₀' := f4 hsP' (hq₀ W).2.1 hsP
  have a₃ : Ent c₃.r (-wAl) := (f7 hsM).1 hsA
  obtain ⟨-, i₀, g₀⟩ := goodQ D hG T tF _ _ ha (resQ T₀.F T₀.g0) c₀ c₀' (h0.pr ▸ hc₀) (h0.pr ▸ hrt) ho hr ∅
  have ok : (T.fr ∅).Ok (𝔞.red c) := (std hP D T tF ∅ c le_rfl).2 _ _ ha
  have hmu : ∀ v, ∀ s ∈ (T.fr ∅).Mu v, s ∈ (T.fr ∅).Gv v := fun v s hs => hs.1
  have hrb := (Chain.rtFacts D hG T tO _ _ ha).2
  obtain ⟨c₄', r₄', u₄', n₄', e₄'⟩ := Chain.levi (T.fr ∅) _ hmu c₃ r₃ m₃
  obtain ⟨c₄, r₄, e₄, n₄⟩ := Chain.movePs (T.fr ∅) _ ok.mul hmu
    (fun v s hs => (hrb _ _).2 (tT.atL _ (T.ovl v) s hs)) c₄' r₄' u₄' n₄' fun v => (Q.map (𝔞.red c₁)).n v 2 0
  have u₄ : Supp {-wAl} c₄.r := e₄ ▸ u₄'
  have m₄ : Supp nM c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have v₄ : Supp vV c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have al : c₃.SameAl c₄ := ⟨fun g => by rw [e₄, e₄'.1], fun v => ((n₄ v).2.1.trans (e₄'.2 v)).symm⟩
  have a₄ : Ent c₄.r (-wAl) := by
    obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).2 m₃).1 a₃
    exact ((Chain.entIff (T.fr ∅) (𝔞.red c) c₄ r₄).2 m₄).2 ⟨g, al.1 g ▸ hg⟩
  have G₀ : (T.fr ∅).Good (𝔞.red c) c₀' := g₀.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have G₃ : (T.fr ∅).Good (𝔞.red c) c₃ := by
    by_cases hp : Ent c₃.r (-wPs)
    · exact Or.inl ⟨hp, Or.inr a₃⟩
    rcases g₀ with x | x
    · obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₀' hr).1 i₀.1).1 x.1
      exact absurd (((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).1 i₃.1).2 ⟨g, p₃.1 g ▸ hg⟩) hp
    refine Or.inr (Or.inr (Or.inl ⟨⟨fun g i j hij hw => ?_, fun v => ⟨i₃.2 v, p₃.2 v ▸ (x.1.2 v).2⟩⟩, a₃⟩))
    by_cases hq : wt i j = -wPs
    · by_contra hne
      exact hp ⟨g, i, j, hq, hne⟩
    · exact q₃ g i j hij (by revert hw hq; revert i j; decide)
  have G₄ : (T.fr ∅).Good (𝔞.red c) c₄ :=
    Or.inr (Or.inr (Or.inl ⟨⟨v₄, fun v => ⟨(n₄ v).1, (n₄ v).2.2 ▸ (sV.2 v).2⟩⟩, a₄⟩))
  have Gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := by
    rcases hQE with x | x
    · exact Or.inr (Or.inr (Or.inl ⟨sV, sE _ x⟩))
    refine Or.inr (Or.inr (Or.inr ⟨sV, sE _ x.1, sE _ x.2, fun v => ?_⟩))
    obtain ⟨g, hg, hne⟩ := tT.bigL _ (T.ovl v)
    exact ⟨g, hg, fun h1 => hne (by rw [(hrb _ _).1 h1, one_pow])⟩
  have L₁ := lineP (T.fr ∅) _ ok c₀' c₃ hr r₃ i₀ i₃ ⟨fun g => (p₃.1 g).symm, fun v => (p₃.2 v).symm⟩
  have L₂ := lineM (T.fr ∅) _ ok c₃ c₄ r₃ r₄ m₃ m₄ al
  have L₃ := lineP (T.fr ∅) _ ok c₄ _ r₄ sR ⟨fun g => supp_mono (by decide) (v₄ g), fun v => (n₄ v).1⟩
    ⟨fun g => supp_mono (by decide) (sV.1 g), fun v => (sV.2 v).1⟩
    ⟨fun g => (v₄ g 2 0 (by decide) (by decide)).trans (sV.1 g 2 0 (by decide) (by decide)).symm, fun v => (n₄ v).2.2⟩
  exact ⟨G₀, ((Relation.ReflTransGen.single ⟨G₃, L₁⟩).tail ⟨G₄, L₂⟩).tail ⟨Gs, L₃⟩⟩
end

