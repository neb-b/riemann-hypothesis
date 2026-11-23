module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartNsmulAndKilledByPPow
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {d : ℕ} (F : FGLaw R d)

private theorem kill_cc : ∀ (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0
  | 0, j => by simp [mulF]
  | N + 1, j => by
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulF F.F N, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨x, l⟩
      fin_cases x
      · exact kill_cc N l
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const j)

private theorem kill_X {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (pt R d i j) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (h3 (i, j))

private theorem kill_zero {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (map_zero ψ)

private theorem kill_one {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) :
    ∀ i j, IsNilpotent ((![a] : Fin 1 → Fin d → S) i j) := fun i j => by
  fin_cases i; exact ha j

private theorem kill_two {a b : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i j, IsNilpotent ((![a, b] : Fin 2 → Fin d → S) i j) := fun i j => by
  fin_cases i
  · exact ha j
  · exact hb j

private theorem kill_add {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (x y : Pt R n d)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (f : PS R 2 d) : nv s (ev ![x, y] f) a = nv s f ![fun l => nv s (x l) a, fun l => nv s (y l) a] := by
  have := (nv_calculus R S s n d a ha).2.2.1 2 d ![x, y] f (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem kill_succ {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (N : ℕ) (j : Fin d) :
    nv s (mulF F.F (N + 1) j) ![a] = nv s (F.F j) ![fun l => nv s (mulF F.F N l) ![a], a] := by
  refine (kill_add s ![a] (kill_one ha) _ _ (kill_cc F N) (fun l => by simp [pt]) (F.F j)).trans ?_
  congr 3
  funext l
  exact kill_X s ![a] (kill_one ha) 0 l

private theorem kill_unitL {c : Fin d → S} (hc : ∀ i, IsNilpotent (c i)) (j : Fin d) :
    nv s (F.F j) ![0, c] = c j := by
  have h := kill_add s ![c] (kill_one hc) 0 (pt R d 0) (fun l => by simp) (fun l => by simp [pt]) (F.F j)
  rw [F.unit j] at h
  have h1 : (fun l => nv s ((0 : Pt R 1 d) l) ![c]) = 0 := funext fun l => kill_zero s _ (kill_one hc)
  have h2 : (fun l => nv s (pt R d (0 : Fin 1) l) ![c]) = c := funext fun l => kill_X s _ (kill_one hc) 0 l
  rw [h1, h2] at h
  exact h.symm.trans (kill_X s _ (kill_one hc) 0 j)

private theorem kill_unitR {b : Fin d → S} (hb : ∀ i, IsNilpotent (b i)) (j : Fin d) :
    nv s (F.F j) ![b, 0] = b j := by
  have h0 := kill_two hb (fun _ => IsNilpotent.zero : ∀ i, IsNilpotent ((0 : Fin d → S) i))
  have h := kill_add s ![b, 0] h0 (pt R d 1) (pt R d 0) (fun l => by simp [pt]) (fun l => by simp [pt]) (F.F j)
  rw [F.comm j] at h
  have h1 : (fun l => nv s (pt R d (1 : Fin 2) l) ![b, 0]) = 0 := funext fun l => kill_X s _ h0 1 l
  have h2 : (fun l => nv s (pt R d (0 : Fin 2) l) ![b, 0]) = b := funext fun l => kill_X s _ h0 0 l
  rw [h1, h2] at h
  exact h.trans (kill_unitL s F hb j)

private theorem kill_sq (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {b c : Fin d → S}
    (hb : ∀ i, b i ∈ K) (hc : ∀ i, c i ∈ K) (j : Fin d) : nv s (F.F j) ![b, c] = b j + c j := by
  have hn : ∀ x ∈ K, IsNilpotent x := fun x hx => ⟨2, by rw [pow_two]; exact hK x hx x hx⟩
  have key : ∀ b c : Fin d → S, (∀ i, b i ∈ K) → (∀ i, c i ∈ K) → nv s (F.F j) ![b, c] =
      ∑ l, s (MvPowerSeries.coeff (Finsupp.single (0, l) 1) (F.F j)) * b l +
        ∑ l, s (MvPowerSeries.coeff (Finsupp.single (1, l) 1) (F.F j)) * c l := by
    intro b c hb hc
    have hm : ∀ i l, (![b, c] : Fin 2 → Fin d → S) i l ∈ K := fun i l => by
      fin_cases i
      · exact hb l
      · exact hc l
    rw [(nv_calculus R S s 2 d ![b, c] (fun i l => hn _ (hm i l))).2.2.2.2.2
      (fun _ _ _ _ => hK _ (hm _ _) _ (hm _ _)), F.const j, map_zero, zero_add, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    rfl
  have h1 := key b 0 hb (fun _ => K.zero_mem)
  have h2 := key 0 c (fun _ => K.zero_mem) hc
  rw [kill_unitR s F (fun i => hn _ (hb i))] at h1
  rw [kill_unitL s F (fun i => hn _ (hc i))] at h2
  rw [key b c hb hc, h1, h2]
  simp

private theorem kill_sqN (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {c : Fin d → S}
    (hc : ∀ i, c i ∈ K) (N : ℕ) : ∀ j, nv s (mulF F.F N j) ![c] = (N : S) * c j := by
  have hn : ∀ i, IsNilpotent (c i) := fun i => ⟨2, by rw [pow_two]; exact hK _ (hc i) _ (hc i)⟩
  induction N with
  | zero => intro j; exact (kill_zero s ![c] (kill_one hn)).trans (by simp)
  | succ N ih =>
    intro j
    rw [kill_succ s F hn, funext ih, kill_sq s F K hK (fun i => K.mul_mem_left _ (hc i)) hc]
    push_cast
    ring

private theorem kill_lin (K : Ideal S) {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i))
    (hc : ∀ i, c i ∈ K) (N : ℕ) (j : Fin d) : nv s (mulF F.F N j) ![c] - (N : S) * c j ∈ K * K := by
  let t := Ideal.Quotient.mk (K * K)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_mul, map_natCast]
  refine ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.2.2.2.1 _ t _).trans ?_
  have h : (fun i l => t ((![c] : Fin 1 → Fin d → S) i l)) = ![fun l => t (c l)] := by
    funext i; fin_cases i; rfl
  rw [h]
  refine kill_sqN (t.comp s) F (K.map t) ?_ (fun i => Ideal.mem_map_of_mem t (hc i)) N j
  intro x hx y hy
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hx
  obtain ⟨y, hy', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hy
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_mul hx' hy')

private theorem kill_nil {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i)) (N : ℕ) (j : Fin d) :
    IsNilpotent (nv s (mulF F.F N j) ![c]) :=
  ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.1 _ (kill_cc F N j)).1

end

theorem bxChart_nsmul_and_killed : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by
  intro R₀ _ B O g F Y hY p R s a hp ha
  have h1 : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) → ∀ N : ℕ,
      N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a]) := by
    intro a ha N
    induction N with
    | zero =>
      rw [zero_nsmul, ← hY.zero R s]
      congr 1
      funext j
      exact (kill_zero _ ![a] (kill_one ha)).symm
    | succ N ih =>
      rw [succ_nsmul, ih, hY.law R s _ _ (kill_nil _ F ha N) ha]
      congr 1
      funext j
      exact (kill_succ _ F ha N j).symm
  refine ⟨h1 a ha, ?_⟩
  let J : Ideal (R : Type) := Ideal.span (insert (p : (R : Type)) (Set.range a))
  have hpJ : (p : (R : Type)) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have h2 : ∀ k : ℕ, ∃ b : Fin g → (R : Type), (∀ i, IsNilpotent (b i)) ∧ (∀ i, b i ∈ J ^ (k + 1)) ∧
      p ^ k • Y R s a = Y R s b := by
    intro k
    induction k with
    | zero =>
      refine ⟨a, ha, fun i => ?_, by simp⟩
      rw [zero_add, pow_one]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    | succ k ih =>
      obtain ⟨b, hb, hbJ, e⟩ := ih
      refine ⟨_, kill_nil _ F hb p, fun i => ?_, by rw [pow_succ', mul_smul, e, h1 b hb p]⟩
      have h3 := kill_lin s.1.toRingHom F (J ^ (k + 1)) hb hbJ p i
      rw [← pow_add] at h3
      have h4 : (p : (R : Type)) * b i ∈ J ^ (k + 1 + 1) := by
        rw [pow_succ' J (k + 1)]
        exact Ideal.mul_mem_mul hpJ (hbJ i)
      simpa using add_mem (Ideal.pow_le_pow_right (by omega : k + 1 + 1 ≤ k + 1 + (k + 1)) h3) h4
  have hfg : J.FG := Submodule.fg_span ((Set.finite_range a).insert _)
  have hle : J ≤ nilradical (R : Type) := by
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hp
    · exact ha i
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  obtain ⟨b, -, hbJ, e⟩ := h2 (n + 1)
  refine ⟨n, ?_⟩
  rw [e, ← hY.zero R s]
  congr 1
  funext i
  have := Ideal.pow_le_pow_right (by omega : n ≤ n + 1 + 1) (hbJ i)
  rw [hn] at this
  simpa using this

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChart
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f φ) {Z : Scheme.{0}}
    (t' : Z ⟶ S') (t : Z ⟶ S) (ht : t' ≫ f = t) :
    ∃ P : (Over.mk t' ⟶ G') →* (Over.mk t ⟶ G), (∀ x, (P x).left = x.left ≫ φ) ∧ Function.Bijective P := by
  subst ht
  let p : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      have := Over.w x
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, h.1.w, ← Category.assoc, this])
  refine ⟨MonoidHom.mk' p fun x y => Over.OverMorphism.ext (h.2 (Over.mk t') x y (p x) (p y) rfl rfl).symm,
    fun _ => rfl, fun x y hxy => ?_, fun z => ?_⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  · refine ⟨Over.homMk (h.1.lift z.left t' (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _

private theorem spec_comp {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact s.1.comp_algebraMap

theorem bxChart_of_nilChart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  intro R₀ _ G _ _ B e hb hm hn O G' _ _ φ hφ g F X hX
  have h0 : ∀ R, e R 0 = 1 := fun R => by
    have := hm R 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  choose P hP hPb using fun (R : LAlg R₀) (s : LHom O R) => exists_push hφ _ _ (spec_comp s)
  let X' : ∀ R : LAlg R₀, ∀ s : LHom O R, (Fin g → (R : Type)) →
      (Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') := fun R s a =>
    @X R _ s.1.toRingHom.toAlgebra a
  choose Y hY using fun (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) => (hb R).2 (P R s (X' R s a))
  have hYl : ∀ R s a, (e R (Y R s a)).left = (X' R s a).left ≫ φ := fun R s a => by rw [hY, hP]
  refine ⟨Y, ⟨fun R s => ?_, fun R R' s f a ha => ?_, fun R s a b ha hb' hab => ?_,
    fun R S s π σ hπσ hσ hπ x hx => ?_, fun R s a b ha hb' => ?_⟩, fun f α A hr hA R s a ha => ?_⟩
  · apply (hb R).1
    rw [hY, h0]
    letI := s.1.toRingHom.toAlgebra
    have : X' R s 0 = 1 := hX.zero R
    rw [this, map_one]
  · apply (hb R').1
    apply Over.OverMorphism.ext
    rw [hn, Over.comp_left, hYl, hYl]
    letI := s.1.toRingHom.toAlgebra
    letI := (f.comp s).1.toRingHom.toAlgebra
    let f' : (R : Type) →ₐ[(O : Type)] (R' : Type) := ⟨f.1.toRingHom, fun _ => rfl⟩
    have := congrArg (fun z => z.left ≫ φ) (hX.nat R R' f' a ha)
    exact (Category.assoc _ _ _).symm.trans this
  · letI := s.1.toRingHom.toAlgebra
    refine hX.inj R a b ha hb' ((hPb R s).1 ?_)
    exact (hY R s a).symm.trans ((congrArg (e R) hab).trans (hY R s b))
  · obtain ⟨z, hz⟩ := (hPb R s).2 (e R x)
    letI := s.1.toRingHom.toAlgebra
    letI := (π.comp s).1.toRingHom.toAlgebra
    let ρ : (R : Type) →ₐ[(O : Type)] (S : Type) := ⟨π.1.toRingHom, fun _ => rfl⟩
    let σ' : (S : Type) →ₐ[(O : Type)] (R : Type) :=
      ⟨σ.1.toRingHom, fun r => congrArg (fun u : LHom O R => u.1 r) hσ⟩
    have h1 : ρ.comp σ' = AlgHom.id _ _ := AlgHom.ext fun r => congrArg (fun u : LHom S S => u.1 r) hπσ
    have h2 : IsNilpotent (RingHom.ker ρ) := ⟨2, hπ.2⟩
    have h3 : spMap ρ ≫ z = 1 := by
      apply (hPb S (π.comp s)).1
      refine Eq.trans ?_ (map_one (P S (π.comp s))).symm
      rw [← h0, ← hx, hn, ← hz]
      apply Over.OverMorphism.ext
      rw [hP, Over.comp_left, Over.comp_left, hP]
      exact Category.assoc _ _ _
    obtain ⟨a, ha, hza⟩ := hX.surj R S ρ σ' h1 h2 z h3
    refine ⟨a, ha, (hb R).1 ?_⟩
    rw [hY, ← hz, hza]
  · apply (hb R).1
    letI := s.1.toRingHom.toAlgebra
    rw [hm, hY, hY, hY, ← map_mul]
    exact congrArg (P R s) (hX.law R a b ha hb')
  · apply (hb R).1
    apply Over.OverMorphism.ext
    letI := s.1.toRingHom.toAlgebra
    rw [← hA s (Y R s a) (X' R s a) (hYl R s a).symm, hYl]
    exact congrArg (fun z => z.left ≫ φ) (hr.2 R a ha)

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0Statement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_derivationPolynomial_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  first | exact @GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | exact GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | (intros; apply GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMem
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CvDiv

variable {C : Type} [Field C]

theorem coeff_alongCv_le {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ}
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, mul_zero, Finset.sum_const_zero]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 hf
  · exact coeff_alongCv_low hn hγ hf

theorem coeff_alongCv_smul {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (c : C)
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv (c • γ) f) = c * PowerSeries.coeff n (alongCv γ f) := by
  rw [coeff_alongCv_le h0 hγ hf, coeff_alongCv_le (fun i => by simp [h0 i])
    (fun i m hm => by simp [hγ i m hm]) hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem isCv_smul {V : VF C} {σ : Type} {γ : σ → PowerSeries C} {c : C} (hc : V.Ge 0 c)
    (h : IsCv V γ) : IsCv V (c • γ) := fun i =>
  ⟨by simp [(h i).1], fun n => by
    simpa only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul] using hc.mul_int ((h i).2 n)⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem step {X : RawChart C d I κ} {V : VF C} (hX : RLaw X V) (g : Fin 2) {c : C} (hc : V.Ge 0 c)
    (m : ℕ) {a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)} (ha : a ∈ Cv X V g)
    (hv : ∀ i, ∀ k < m, PowerSeries.coeff k (a.1 i) = 0) :
    ∃ b ∈ Cv X V g, ∀ k ≤ m, (∀ i, PowerSeries.coeff k (b.1 i) = c * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (b.2 q) = c * PowerSeries.coeff k (a.2 q) := by
  classical
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hX.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hord : ∀ k, k < m → ∀ i, PowerSeries.coeff k (γ i) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i
      have e1 := coeff_alongCv_le h0 (fun i m' hm' => ih m' hm' (by omega) i) (hlg0 i)
      rw [h1 i, hv i k hk] at e1
      simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1
      exact e1.symm
  refine ⟨(fun i => alongCv (c • γ) (X.lg i), fun q => (c • lam) q - alongCv (c • γ) (X.sg (X.u (1 - g) q))),
    ⟨c • γ, c • lam, isCv_smul hc hγ, isCv_smul hc hlam, fun _ => rfl, fun _ => rfl⟩, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [← h1 i]
    exact coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (hlg0 i)
  · rw [h2 q]
    simp only [map_sub, Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
    rw [coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (X.constantCoeff_sg (hX.axes 0) _)]
    ring

end GlobalTheory.RowLaw.CvDiv

namespace GlobalTheory.RowLaw


open CvDiv in
theorem cv_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g N hN a ha
  obtain ⟨hzero, hadd, hneg, -⟩ := _root_.GlobalTheory.RowLaw.cv_group C V d I κ X hX g
  have hN0 : (N : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hN
    exact WithTop.top_ne_zero hN
  have hc : V.Ge 0 (N : C)⁻¹ := by
    have h := V.v.map_mul (N : C) (N : C)⁻¹
    rw [mul_inv_cancel₀ hN0, V.v.map_one, hN, zero_add] at h
    unfold VF.Ge
    rw [← h]
    exact le_rfl
  have hns : ∀ s ∈ Cv X V g, ∀ n : ℕ, (n : C) • s ∈ Cv X V g := by
    intro s hs n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul]
      exact hadd _ ih _ hs
  have key : ∀ m : ℕ, ∃ s ∈ Cv X V g, ∀ k < m,
      (∀ i, PowerSeries.coeff k (s.1 i) = (N : C)⁻¹ * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (s.2 q) = (N : C)⁻¹ * PowerSeries.coeff k (a.2 q) := by
    intro m
    induction m with
    | zero => exact ⟨0, hzero, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨s, hs, hsa⟩ := ih
      have hr : a + -((N : C) • s) ∈ Cv X V g := hadd _ ha _ (hneg _ (hns s hs N))
      obtain ⟨b, hb, hba⟩ := step hX g hc m hr (fun i k hk => by
        simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add (f := _),
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hsa k hk).1 i]
        field_simp
        ring)
      refine ⟨s + b, hadd _ hs _ hb, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
      · simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add (f := _),
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).1 i]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add (f := _),
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).2 q]
        field_simp
        ring
  choose s hs hsa using key
  refine _root_.GlobalTheory.RowLaw.cv_closed_under_limits C V d I κ X hX g s _ hs fun m => ⟨m + 1, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [(hsa n m (by omega)).1 i]
    simp
  · rw [(hsa n m (by omega)).2 q]
    simp

end GlobalTheory.RowLaw
end

