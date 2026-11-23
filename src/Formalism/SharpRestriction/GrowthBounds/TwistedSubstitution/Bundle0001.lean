module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.PlaneCoeff

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.CommPresIsoSub
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G

section Commutant

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)

theorem comm_Umon (A : Module.End K V) (hA : ∀ a b, A * E a b = E a b * A) : ∀ u ∈ Umon E, A * u = u * A := by
  intro u hu
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact hA ab.1 ab.2
  | one => simp
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem comm_pres_isoSub (A : Module.End K V) (hA : ∀ a b, A * E a b = E a b * A) (mu : Fin n → ℤ) :
    ∀ x ∈ isoSub E mu, A x ∈ isoSub E mu := by
  intro x hx
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    have h1 : A (u v) = u (A v) := by
      have := comm_Umon E A hA u hu
      simpa only [Module.End.mul_apply] using congrArg (fun f => f v) this
    rw [h1]
    by_cases h0 : A v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨u, hu, A v, ⟨h0, ?_, ?_⟩, rfl⟩
      · have hw := hv.2.1
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
        intro a
        have hc : E a a (A v) = A (E a a v) := by
          simpa only [Module.End.mul_apply] using (congrArg (fun f => f v) (hA a a)).symm
        have hwa := hw a
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hwa ⊢
        rw [hc, ← map_smul, ← map_sub, hwa, map_zero]
      · intro a b hab
        have hc : E a b (A v) = A (E a b v) := by
          simpa only [Module.End.mul_apply] using (congrArg (fun f => f v) (hA a b)).symm
        rw [hc, hv.2.2 a b hab, map_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem comm_isoProj (A : Module.End K V) (hA : ∀ mu, ∀ x ∈ isoSub E mu, A x ∈ isoSub E mu)
    (ee : (Fin n → ℤ) → Module.End K V) (hee : ∀ mu, IsIsoProj E mu (ee mu))
    (hdec : ∀ G : V, ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee mu G ∧ ∀ mu, ee mu G ∈ isoSub E mu)
    (lam : Fin n → ℤ) : ee lam * A = A * ee lam := by
  have hproj : ∀ mu y, y ∈ isoSub E mu → ee lam y = if mu = lam then y else 0 := by
    intro mu y hy
    split_ifs with h
    · subst h; exact (hee mu).1 y hy
    · exact (hee lam).2 mu h y hy
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, hx, hm⟩ := hdec x
  simp only [Module.End.mul_apply]
  have hAx : A x = ∑ mu ∈ T, A (ee mu x) := by
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  have hex : ee lam x = ∑ mu ∈ T, ee lam (ee mu x) := by
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hAx, hex, map_sum, map_sum]
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [hproj mu _ (hA mu _ (hm mu)), hproj mu _ (hm mu)]
  split_ifs <;> simp

end Commutant

section Family

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

def jointE (ka : ι → Fin n → ℤ) : Module.End K V :=
  ((Finset.univ : Finset ι).toList.map fun i => ee i (ka i)).prod

theorem prod_split (l : List (Module.End K V)) (hl : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) (a : Module.End K V)
    (ha : a ∈ l) : ∃ rest : Module.End K V, l.prod = a * rest ∧ l.prod = rest * a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hcl : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x := fun x hx y hy =>
      hl x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have hcomm : ∀ c ∈ b :: l, c * l.prod = l.prod * c := by
      intro c hc
      have : Commute c l.prod := Commute.list_prod_right _ _ fun y hy => hl c hc y (List.mem_cons_of_mem _ hy)
      exact this.eq
    rcases List.mem_cons.1 ha with h | h
    · subst h
      exact ⟨l.prod, by simp, by rw [List.prod_cons, hcomm a (List.mem_cons_self)]⟩
    · obtain ⟨rest, h1, h2⟩ := ih hcl h
      refine ⟨b * rest, ?_, ?_⟩
      · rw [List.prod_cons, h1, ← mul_assoc, hl b List.mem_cons_self a (List.mem_cons_of_mem _ h), mul_assoc]
      · rw [List.prod_cons, h2, mul_assoc]

variable {E ee}

theorem jointE_comm (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) :
    ∀ x ∈ (Finset.univ : Finset ι).toList.map (fun i => ee i (ka i)),
      ∀ y ∈ (Finset.univ : Finset ι).toList.map (fun i => ee i (ka i)), x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
  exact hcomm i i' _ _

theorem jointE_factor (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) (i : ι) :
    ∃ rest, jointE ee ka = ee i (ka i) * rest ∧ jointE ee ka = rest * ee i (ka i) :=
  prod_split _ (jointE_comm hcomm ka) _ (List.mem_map.2 ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), rfl⟩)

theorem jointE_isJProj (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ) :
    IsJProj E {ka} (jointE ee ka) := by
  constructor
  · intro lam hlam x hx
    rw [Set.mem_singleton_iff] at hlam
    subst hlam
    have hfix : ∀ i, ee i (lam i) x = x := fun i =>
      (hee i (lam i)).1 x ((Submodule.mem_iInf _).1 hx i)
    unfold jointE
    induction (Finset.univ : Finset ι).toList with
    | nil => simp
    | cons i l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, hfix]
  · intro mu hmu x hx
    have hne : mu ≠ ka := fun h => hmu (Set.mem_singleton_iff.2 h)
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ ka i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨rest, -, h2⟩ := jointE_factor hcomm ka i
    rw [h2, Module.End.mul_apply, (hee i (ka i)).2 (mu i) hi x ((Submodule.mem_iInf _).1 hx i), map_zero]

theorem jointE_mem (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (ka : ι → Fin n → ℤ) (F : V) (i : ι) : jointE ee ka F ∈ isoSub (E i) (ka i) := by
  obtain ⟨rest, h1, -⟩ := jointE_factor hcomm ka i
  rw [h1, Module.End.mul_apply]
  obtain ⟨_, _, h⟩ := hdec i (rest F)
  exact h (ka i)

theorem jointE_pres (P : Submodule K V) (hP : ∀ i mu, ∀ F ∈ P, ee i mu F ∈ P) (ka : ι → Fin n → ℤ) :
    ∀ F ∈ P, jointE ee ka F ∈ P := by
  intro F hF
  unfold jointE
  induction (Finset.univ : Finset ι).toList with
  | nil => simpa using hF
  | cons i l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply]; exact hP i _ _ ih

end Family

end Formalism.MainNotions.TestSideWords
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def NSConcl (CH CE C6 C18 : ℝ) (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m : ℕ} (r : ℕ) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r] [NeZero K]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (cP κ DX : ℕ)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∃ (J : ℕ) (_ : NeZero J) (Dt : SignedChainData p O r J) (F2 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)),
    Dt.Hyp CH ∧ 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c ∧ Dt.XX F2 ∧ vBB (O := O) p F2 = 0 ∧
    ∀ Gp R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O),
      (∀ mo, geQ (vK p (Gp.coeff mo)) 0) → Dt.YY C6 C18 Gp →
      (∀ mo, geQ (vK p (R.coeff mo)) (Dt.c - Dt.EE CE)) →
      (∀ mo ∈ Gp.support ∪ R.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) →
      geQ (vBB (O := O) p (Dt.ph (Gp + R))) (Dt.n0 - Dt.kp) →
      leQ (vK p (Dt.Bform F2 (Dt.ph (Gp + R)))) (Dt.EE CE + 2 * Dt.kp + Dt.n0 - Dt.kp) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock G (∑ q, sig q) / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O))

theorem nsAt_of (CH CE C6 C18 : ℝ) (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r]
    [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (c0 cP κ : ℕ) (bD : ℝ)
    {nb : ℕ} (B : Fin nb → RRing O n' (r + K)) (DX : ℕ) (hDX : (DX : ℝ) ≤ bD)
    (h : ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => symP p O hk hrk Fr cP (p ^ G') (B b))) →
      HasMultideg G d → InWj w G 0 → ¬ InWj w G 1 →
      NSConcl CH CE C6 C18 p r d deg K hk Fr N₁ G' Y cP κ DX G) :
    NSAt CH CE C6 C18 p w r TT d deg K hk hrk Fr N₁ G' Y c0 cP κ bD B :=
  ⟨DX, hDX, h⟩

def DataII (C CLa : ℝ) (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (F : Frames n' r) (nb : ℕ) (B : Fin nb → RRing O n' (r + K)) : Prop :=
  UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w ∧
  Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar ∧
  FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F ∧
  (∃ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) ∧
    ∀ i, B i ∈ Gen O p K F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
      (G2d F (flatDeg lam0) E')) ∧
  LinearIndependent O B ∧ (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T)

def MemStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b =>
        symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))) →
      MemAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) G

def Proposition5At (C CD CLa CH CE C6 C18 : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∃ DX : ℕ, (DX : ℝ) ≤ CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b =>
        symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))) →
      HasMultideg G (dT TT lam0) → InWj w G 0 → ¬ InWj w G 1 →
      MemAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) G →
      NSConcl CH CE C6 C18 p r (dT TT lam0) (flatDeg lam0) K hk F (orbitWindowCount r de h x) (goodG' r de h x) Y
        (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0)) DX G

theorem nsStep_of (C CD CLa CH CE C6 C18 : ℝ) (hM : MemStep C CLa) (hP : Proposition5At C CD CLa CH CE C6 C18) :
    NSStep C CD CLa CH CE C6 C18 := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K
    _ _ hk hrk F hF E' hE' nb B hB hli hc
  have hD : DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B :=
    ⟨hSet, H, hF, ⟨E', hE', hB⟩, hli, hc⟩
  obtain ⟨DX, hDX, hP'⟩ := hP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
  exact nsAt_of CH CE C6 C18 p w r TT (dT TT lam0) (flatDeg lam0) K hk hrk F _ _ Y c0 _ _ _ B DX hDX
    fun G h1 h2 h3 h4 => hP' G h1 h2 h3 h4
      (hM p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD G h1)

def RestMEM (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → MemStep C CLa

def Proposition5Gram (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → Proposition5At C CDf CLa CH CE C6 C18

theorem restNS_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hM : RestMEM D CLa Ck Crk Cdeg) (hP : Proposition5Gram D CLa Ck Crk Cdeg CH CE C6 C18) :
    RestNS D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA
  obtain ⟨C₁, h1, hM'⟩ := hM hA
  obtain ⟨CDf, C₂, h2, h3, hP'⟩ := hP hA
  refine ⟨CDf, max C₁ C₂, h2, lt_max_of_lt_left h1, fun C hC => ?_⟩
  exact nsStep_of C CDf CLa CH CE C6 C18 (hM' C (le_trans (le_max_left _ _) hC)) (hP' C (le_trans (le_max_right _ _) hC))

end Formalism.MainNotions.TestSideWords
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TransportMon
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.PlaneGramData Formalism.MainNotions.Pf14

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def LowDiv (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x (a : Fin r), lowP Fr p x ∣ mo (plVar Fr hk nL x a)) ∧ ∀ x (b : Fin K), lowP Fr p x ∣ mo (noVar Fr hk nL x b)

theorem inLow_add (rho : TL J nL r × Fin (r + K) → ℕ) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ)
    (h : LowDiv Fr p hk nL mo₂) : InLow Fr p hk nL rho (mo₁ + mo₂) ↔ InLow Fr p hk nL rho mo₁ := by
  have e1 : ∀ x a, (mo₁ + mo₂) (plVar Fr hk nL x a) % lowP Fr p x = mo₁ (plVar Fr hk nL x a) % lowP Fr p x := by
    intro x a
    obtain ⟨k, hk'⟩ := h.1 x a
    rw [Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]
  have e2 : ∀ x b, (mo₁ + mo₂) (noVar Fr hk nL x b) % lowP Fr p x = mo₁ (noVar Fr hk nL x b) % lowP Fr p x := by
    intro x b
    obtain ⟨k, hk'⟩ := h.2 x b
    rw [Finsupp.add_apply, hk', Nat.add_mul_mod_self_left]
  unfold InLow
  simp only [e1, e2]

theorem lowP_pos (hp : 0 < p) (x : TL J nL r) : 0 < lowP Fr p x := pow_pos hp _

theorem plMon_add (hp : 0 < p) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ) (h : LowDiv Fr p hk nL mo₂) :
    plMon Fr p hk nL (mo₁ + mo₂) = plMon Fr p hk nL mo₁ + plMon Fr p hk nL mo₂ := by
  ext ⟨x, a⟩
  simp only [plMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
  obtain ⟨c, hc⟩ := h.1 x a
  rw [hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]

theorem noMon_add (hp : 0 < p) (mo₁ mo₂ : TV n' (m + 1) →₀ ℕ) (h : LowDiv Fr p hk nL mo₂) :
    noMon Fr p hk nL (mo₁ + mo₂) = noMon Fr p hk nL mo₁ + noMon Fr p hk nL mo₂ := by
  ext ⟨x, b⟩
  simp only [noMon, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
  obtain ⟨c, hc⟩ := h.2 x b
  rw [hc, Nat.add_mul_div_left _ _ (lowP_pos Fr p nL hp x), Nat.mul_div_cancel_left _ (lowP_pos Fr p nL hp x)]

theorem lowDiv_add {mo₁ mo₂ : TV n' (m + 1) →₀ ℕ} (h1 : LowDiv Fr p hk nL mo₁) (h2 : LowDiv Fr p hk nL mo₂) :
    LowDiv Fr p hk nL (mo₁ + mo₂) :=
  ⟨fun x a => by rw [Finsupp.add_apply]; exact dvd_add (h1.1 x a) (h2.1 x a),
   fun x b => by rw [Finsupp.add_apply]; exact dvd_add (h1.2 x b) (h2.2 x b)⟩

theorem lowDiv_zero : LowDiv Fr p hk nL (0 : TV n' (m + 1) →₀ ℕ) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

def GeoOK : Prop :=
  ∀ (j : ℕ), j < Fr.J → ∀ y ∈ Fr.letters (j : ℤ), ∀ x' : TL J nL r,
    posOf n' (posTL Fr x') = posOf n' y → lowP Fr p x' ∣ p ^ Fr.dist (j : ℤ) y

theorem lowDiv_single (v : TV n' (m + 1)) (N : ℕ)
    (h : ∀ x' : TL J nL r, (∃ a, plVar Fr hk nL x' a = v) ∨ (∃ b, noVar Fr hk nL x' b = v) → lowP Fr p x' ∣ N) :
    LowDiv Fr p hk nL (Finsupp.single v N) := by
  constructor
  · intro x a
    rw [Finsupp.single_apply]
    split_ifs with hv
    · exact h x (Or.inl ⟨a, hv.symm⟩)
    · exact dvd_zero _
  · intro x b
    rw [Finsupp.single_apply]
    split_ifs with hv
    · exact h x (Or.inr ⟨b, hv.symm⟩)
    · exact dvd_zero _

theorem lowDiv_phVar (hG : GeoOK Fr p nL) (j : ℕ) (hj : j < Fr.J) (y : ℤ) (hy : y ∈ Fr.letters (j : ℤ))
    (c : Fin (m + 1)) (e : ℕ) :
    LowDiv Fr p hk nL (Finsupp.single (posOf n' y, c) (p ^ Fr.dist (j : ℤ) y * e)) := by
  apply lowDiv_single
  intro x' hx'
  have hpos : posOf n' (posTL Fr x') = posOf n' y := by
    rcases hx' with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact congrArg Prod.fst ha
    · exact congrArg Prod.fst hb
  exact Dvd.dvd.mul_right (hG j hj y hy x' hpos) e

def LD {R : Type*} [CommSemiring R] (P : MvPolynomial (TV n' (m + 1)) R) : Prop :=
  ∀ mo ∈ P.support, LowDiv Fr p hk nL mo

theorem LD_add {R : Type*} [CommSemiring R] {P Q : MvPolynomial (TV n' (m + 1)) R} (hP : LD Fr p hk nL P)
    (hQ : LD Fr p hk nL Q) : LD Fr p hk nL (P + Q) := by
  intro mo hmo
  rcases Finset.mem_union.1 (MvPolynomial.support_add hmo) with h | h
  · exact hP mo h
  · exact hQ mo h

theorem LD_mul {R : Type*} [CommSemiring R] {P Q : MvPolynomial (TV n' (m + 1)) R} (hP : LD Fr p hk nL P)
    (hQ : LD Fr p hk nL Q) : LD Fr p hk nL (P * Q) := by
  intro mo hmo
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hmo)
  exact lowDiv_add Fr p hk nL (hP a ha) (hQ b hb)

theorem LD_C {R : Type*} [CommSemiring R] (c : R) : LD Fr p hk nL (C c : MvPolynomial (TV n' (m + 1)) R) := by
  intro mo hmo
  rw [mem_support_iff, coeff_C] at hmo
  split_ifs at hmo with h0
  · subst h0
    exact lowDiv_zero Fr p hk nL
  · exact absurd rfl hmo

theorem LD_monomial {R : Type*} [CommSemiring R] (mo : TV n' (m + 1) →₀ ℕ) (c : R) (h : LowDiv Fr p hk nL mo) :
    LD Fr p hk nL (monomial mo c) := by
  intro mo' hmo
  rw [Finset.mem_singleton.mp (support_monomial_subset hmo)]
  exact h

theorem LD_prod {R : Type*} [CommSemiring R] {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial (TV n' (m + 1)) R)
    (h : ∀ i ∈ s, LD Fr p hk nL (f i)) : LD Fr p hk nL (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using LD_C Fr p hk nL (1 : R)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact LD_mul Fr p hk nL (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LD_phSeg (hG : GeoOK Fr p nL) {O : Type} [CommRing O] (j : ℕ) (hj : j < Fr.J) (x : SegRing O r K)
    (hx : x ∈ MvPolynomial.supported O {v : ℤ × Fin (r + K) | v.1 ∈ Fr.letters (j : ℤ)}) :
    LD Fr p hk nL (rename (castV hk) (phSeg O K p Fr (j : ℤ) x)) := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hx
  induction hx using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    rw [phSeg, aeval_X, map_pow, rename_X, X_pow_eq_monomial]
    apply LD_monomial
    have := lowDiv_phVar Fr p hk nL hG j hj w.1 hw (Fin.cast (by omega) w.2) 1
    simpa [castV] using this
  | algebraMap c =>
    rw [AlgHom.commutes, algebraMap_eq, rename_C]
    exact LD_C Fr p hk nL c
  | add a b _ _ ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact LD_add Fr p hk nL ha hb
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul]
    exact LD_mul Fr p hk nL ha hb

end Formalism.MainNotions.TestSideWords
end
end

