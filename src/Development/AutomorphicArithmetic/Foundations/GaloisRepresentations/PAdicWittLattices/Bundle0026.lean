module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanPureDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFullOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pFullOf :
    FullOf := by
  intro p _ D R _ _ gb S s N o k _ _ t J
  have hp : p.Prime := Fact.out
  have hts : t ≫ s = spMap (Spec.preimage (t ≫ s)).hom := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', -⟩ := o.geom k t _ hts
  have hLB : (o.P.pull (Over.Hom.left (lift (𝟙 o.A) (𝟙 o.A)))).IsLB := pull_isLB o.isLB _
  have hpos : ∀ r : ℕ, 0 < p ^ r := fun r => pow_pos hp.pos r
  refine HeckeGen.exists_join (fun c g => g ≫ o.act.act c) _ ?_ ?_ ?_ ?_ ?_ J (fun r => I'.ζ (p ^ r))
    (fun r => I'.ev (p ^ r)) (fun r => I'.ζ_prim _ (hpos r)) ?_ (fun r x y => I'.add _ x y)
    (fun r b x => I'.lin _ b x) (fun r x => I'.ker _ (hpos r) x) (fun r q => I'.onto _ (hpos r) q) ?_
    (fun r x y => I'.isom _ (hpos r) x y)
  · intro c a b
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  · intro n hn g g' hg hg'
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S o.A _ o.ab hLB k t n hn
      (HeckeGen.natCast_ne_zero_of_hom (Spec.preimage (t ≫ s)).hom n hn) g g' hg hg'
    obtain ⟨z, rfl⟩ := HeckeGen.unitOn_bij.2 e
    exact ⟨z, he⟩
  · intro n g g' z z' h1 h2
    exact HeckeGen.unitOn_bij.1 (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab hLB h1 h2)
  · intro n j g g' z h
    have hu : unitOn (z ^ j) = unitOn z ^ j := by
      unfold unitOn
      exact map_pow _ _ _
    rw [hu, Nat.cast_mul]
    exact GlobalTheory.WeilIsogeny.weilIs_pow GlobalTheory.globalFns_holds o.ab hLB j h
  · intro n j g g' z h
    haveI := isMonHom_mulA (A := o.A) j
    have hiso := GlobalTheory.HeckeWeilValue.lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ j
    have e1 : ∀ x : Over.mk t ⟶ o.A, x ≫ Out.mulA o.A j = x ^ j := fun x => by
      rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have h' := h
    rw [← e1, ← e1] at h'
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab hLB hLB (Out.mulA o.A j) hiso h'
    rw [Nat.cast_mul]
    exact this
  · intro r s'
    rw [pow_add]
    exact I'.ζ_pow _ _ (hpos r) (hpos s')
  · intro r s' x
    rw [pow_add]
    exact I'.tower _ _ (hpos r) (hpos s') x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitForget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isIso_hecke {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N k : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} {o' : GObj gb (N * k) s} {o : GObj gb N s} {ψ : o'.A ⟶ o.A}
    (h : IsGHecke (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) (k ^ 2) k N o' o ψ) : IsIso ψ := by
  obtain ⟨f, -, e⟩ := GlobalTheory.HomDescent.exists_desc S o'.A o.A o'.A
    (gHeckeSub o' (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) N) ψ h.isMonHom h.cover (𝟙 _) inferInstance
    (fun a ha => by rw [gHeckeSub_smul_id_eq_one o' a ha, Category.comp_id])
  have : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover h.cover
  refine ⟨f, e, ?_⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi ψ.left, ← Over.comp_left, ← Over.comp_left, ← Category.assoc, e]
  simp

private theorem pol_hecke {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N k : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} (hk : 0 < k) {o' : GObj gb (N * k) s} {o : GObj gb N s} {ψ : o'.A ⟶ o.A}
    (h : IsGHecke (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) (k ^ 2) k N o' o ψ) :
    LBIso o'.P (o.P.pull (Hecke.sq2 ψ)) := by
  have h0 := h.pol
  rw [Nat.div_self (pow_pos hk 2)] at h0
  obtain ⟨h0⟩ := h0
  have l1 : (Hecke.lbPow o'.P 1).IsLB := LB.isLB_linComb o'.isLB _ _
  have l2 : (o'.P.pull (𝟙 _)).IsLB := pull_isLB o'.isLB _
  have i1 : LBIso (o'.P.pull (𝟙 _)) (Hecke.lbPow o'.P 1) := by
    refine (GlobalTheory.PrimNorm.lbIso_iff o'.isLB _ _ _ _).2 ?_
    simp
  exact LBIso.trans o'.isLB l2 (pull_isLB o.isLB _) (GlobalTheory.SiegLower.lbIso_pull_id o'.isLB)
    (LBIso.trans l2 l1 (pull_isLB o.isLB _) i1 h0)

private theorem aux (hMap : MapOfIso) (hSelf : TransSelf) (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (R : Type) [Field R] [Algebra ℚ R] (gb : GBase D.toG R) (N : Lv p) (c : ℕ) (hc : c.Coprime p)
    (X : GenModel gb N.1) (X' : GenModel gb (N.1 * c)) :
    ∃ π Φ, Wit L 1 X' X π Φ ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hc; omega
  have hN : 0 < N.1 := by have := N.2.1; omega
  obtain ⟨π, ⟨hπ, o', ψ, hG, ⟨m'⟩⟩, hf, he, hs⟩ := HeckeGen.exists_gHeckeMap_finite_etale_surjective p D R gb
    (c • LinearMap.id) (c ^ 2) c N.1 (hc.pow_left 2) hc N.2.1 N.2.2
    (fun x y => by simp [LinearMap.smul_apply]; ring) (fun x => ⟨x, rfl⟩) dvd_rfl X X'
  have hI : IsIso ψ := isIso_hecke hG
  obtain ⟨m, -⟩ := hMap D.toG R gb X'.X X'.s N.1 (X'.univ.forgetMul hN cpos) o' ψ hI hG.isMonHom hG.act
    (pol_hecke cpos hG) (fun y => (hG.eta y).symm)
  obtain ⟨φ⟩ := Unique.gObjMap_comp m m'
  rw [Category.id_comp] at φ
  exact ⟨π, (𝟙 X'.univ.A : X'.univ.A ⟶ X'.univ.A).left ≫ φ.φ,
    ⟨hπ, X'.univ.forgetMul hN cpos, 𝟙 _, φ, (hSelf p D G L R gb X'.X X'.s N).2 c hN cpos X'.univ, rfl⟩, hf, he, hs⟩

theorem UpperTheory.Gal.G3.pWitForget :
    MapOfIso → TransSelf → WitForget := by
  intro hMap hSelf p _ D G L R _ _ gb N M hdiv X X'
  obtain ⟨M, hM⟩ := M
  obtain ⟨c, rfl⟩ := hdiv
  exact aux hMap hSelf p D G L R gb N c (Nat.Coprime.coprime_mul_left hM.2) X X'
end

