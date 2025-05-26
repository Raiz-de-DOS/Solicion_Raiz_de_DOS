package org.sbpo2025.challenge;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.apache.commons.lang3.time.StopWatch;

import ilog.concert.IloConstraint;
import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearIntExpr;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.cplex.IloCplex;

public class ChallengeSolver {
    private final long MAX_RUNTIME = 1000 * 60 * 10; // milliseconds; 10 minutes
    private final long MAX_REMAINING_SECONDS_TO_STOP = 10; // seconds; 1 minute
    private final double EPSILON = .50;
    private final double MINUS_INF = Double.MIN_VALUE;
    private final double TOLERANCE = Math.exp(-6);

    protected List<Map<Integer, Integer>> orders;
    protected List<Map<Integer, Integer>> aisles;
    protected int nItems;
    protected int waveSizeLB;
    protected int waveSizeUB;

    public ChallengeSolver(
            List<Map<Integer, Integer>> orders, List<Map<Integer, Integer>> aisles, int nItems, int waveSizeLB, int waveSizeUB) throws IloException {
        this.orders = orders;
        this.aisles = aisles;
        this.nItems = nItems;
        this.waveSizeLB = waveSizeLB;
        this.waveSizeUB = waveSizeUB;
    }

    public ChallengeSolution solve(StopWatch stopWatch) throws IloException {
        int cantPasillos = this.aisles.size();
        double epsilon = 1 / (double) cantPasillos;
        double rango_k = (Math.log(this.waveSizeUB - ((double) this.waveSizeLB / cantPasillos)) - Math.log(epsilon)) / (Math.log(2.0));
        List<Boolean> dictWSol = List.of();
        List<Boolean> dictASol = List.of();
        IloCplex prob = new IloCplex();
        prob.setOut(null);
  
        System.out.println(String.format("Aisles: %d", cantPasillos));
        System.out.println(String.format("LB: %d", this.waveSizeLB));
        System.out.println(String.format("UB: %d", this.waveSizeUB));

        if (cantPasillos <= rango_k) {
            System.out.println("Chose fixed aisles");
            List<List<Boolean>> solucionActual = planteoPasillosFijos(prob);
            dictWSol = solucionActual.get(0);
            dictASol = solucionActual.get(1);
        } else {
            System.out.println("Chose binary search");
            List<List<Boolean>> solucionActual = planteo_busqueda_binaria(prob, epsilon, stopWatch);
            dictWSol = solucionActual.get(0);
            dictASol = solucionActual.get(1);
        }
        List<Boolean> finalDictWSol = dictWSol;
        List<Boolean> finalDictASol = dictASol;
        Set<Integer> finalOrder = IntStream.range(0, orders.size()).filter(finalDictWSol::get).boxed().collect(Collectors.toSet());
        Set<Integer> finalAisle = IntStream.range(0, aisles.size()).filter(finalDictASol::get).boxed().collect(Collectors.toSet());
        return new ChallengeSolution(finalOrder, finalAisle);
    }

    private List<List<Boolean>> planteoPasillosFijos(IloCplex prob) throws IloException {
        List<List<Boolean>> resPasillos = new ArrayList<>();

        if (this.orders.isEmpty() || this.aisles.isEmpty()) {
            throw new IloException("Error: No hay órdenes o pasillos disponibles.");
        }

        IloIntVar[] listaW1 = new IloIntVar[this.orders.size()];
        IloIntVar[] listaA1 = new IloIntVar[this.aisles.size()];

        // Order belongs to wave
        for (int o = 0; o < this.orders.size(); o++) {
            listaW1[o] = prob.boolVar(String.format("W_%d", o));
        }

        //Aisle is used
        for (int a = 0; a < this.aisles.size(); a++) {
            listaA1[a] = prob.boolVar(String.format("A_%d", a));
        }

        // The amount of items that are taken in the Wave is in range
        IloLinearIntExpr suma = prob.linearIntExpr();
        for (int o = 0; o < this.orders.size(); o++) {
            for (Map.Entry<Integer, Integer> i : this.orders.get(o).entrySet()) {
                suma.addTerm(i.getValue(), listaW1[o]);
            }
        }
        prob.addLe(suma, this.waveSizeUB);
        prob.addGe(suma, this.waveSizeLB);

        // All items grabbed from an aisle have stock
        for (int i = 0; i < this.nItems; i++) {
            IloLinearIntExpr izq = prob.linearIntExpr();
            IloLinearIntExpr der = prob.linearIntExpr();

            for (int o = 0; o < this.orders.size(); o++) {
                int u_oi = this.orders.get(o).getOrDefault(i, 0);
                izq.addTerm(u_oi, listaW1[o]);
            }
            for (int a = 0; a < this.aisles.size(); a++) {
                int u_ai = this.aisles.get(a).getOrDefault(i, 0);
                der.addTerm(u_ai, listaA1[a]);
            }
            prob.addLe(izq, der); // Agrega la restricción
        }

        double maximo = MINUS_INF;
        double valorObjetivoActual;
        List<Boolean> valoresW = List.of();
        List<Boolean> valoresA = List.of();
        prob.addMaximize(suma);
        prob.setParam(IloCplex.Param.MIP.Tolerances.AbsMIPGap, TOLERANCE);
        IloLinearIntExpr sumaDeA = prob.linearIntExpr();
        for (int a = 0; a < this.aisles.size(); a++) {
            sumaDeA.addTerm(1, listaA1[a]);
        }

        for (int aPrima = 1; aPrima < this.aisles.size() + 1 && maximo * aPrima <= this.waveSizeUB ; aPrima++) {
            //int aPrima = 2;
            //La cantidad de pasillos usados es A* (pasado por parámetro)

            IloConstraint restriccionA = prob.addEq(sumaDeA, aPrima);

            if (prob.solve()) {
                //Resolver el lp
                valorObjetivoActual = prob.getObjValue() / aPrima;

                if (maximo <= valorObjetivoActual) {
                    maximo = valorObjetivoActual;
                    System.out.println(valorObjetivoActual);
                    valoresW = new ArrayList<>();
                    valoresA = new ArrayList<>();

                    for (IloIntVar w : listaW1) {
                        valoresW.add(prob.getValue(w) >= 0.5);
                    }

                    for (IloIntVar a : listaA1) {
                        valoresA.add(prob.getValue(a) >= 0.5);
                    }
                }
            } else {
                System.out.println(String.format("Infactible para a'=%d", aPrima));
            }
            prob.remove(restriccionA);
        }
        //System.out.println(prob.getValue(suma) / prob.getValue(sumaDeA));
        resPasillos.add(valoresW);
        resPasillos.add(valoresA);
        return resPasillos;
    }

    private List<List<Boolean>> planteo_busqueda_binaria(IloCplex prob, double epsilon, StopWatch stopWatch) throws IloException {
        List<List<Boolean>> resBB = new ArrayList<>();

        if (this.orders.isEmpty() || this.aisles.isEmpty()) {
            throw new IloException("Error: There are know available orders or aisles.");
        } //Exception if some input is empty

        IloIntVar[] listaW1 = new IloIntVar[this.orders.size()];
        IloIntVar[] listaA1 = new IloIntVar[this.aisles.size()];

        //If the order is in the wave
        for (int o = 0; o < this.orders.size(); o++) {
            listaW1[o] = prob.boolVar(String.format("W_%d", o));
        }

        //If the aisle is used
        for (int a = 0; a < this.aisles.size(); a++) {
            listaA1[a] = prob.boolVar(String.format("A_%d", a));
        }

        IloNumVar z = prob.numVar(0, waveSizeUB, "z"); //Creates a real variable

        //The amount of items which are in the wave is bounded
        IloLinearIntExpr suma = prob.linearIntExpr();
        for (int o = 0; o < this.orders.size(); o++) {
            for (Map.Entry<Integer, Integer> i : this.orders.get(o).entrySet()) {
                suma.addTerm(i.getValue(), listaW1[o]);
            }
        }
        prob.addLe(suma, this.waveSizeUB);
        prob.addGe(suma, this.waveSizeLB);

        //Every item grabbed from an aisle has stock
        for (int i = 0; i < this.nItems; i++) {
            IloLinearNumExpr izq = prob.linearNumExpr();
            IloLinearNumExpr der = prob.linearNumExpr();

            for (int o = 0; o < this.orders.size(); o++) {
                int u_oi = this.orders.get(o).getOrDefault(i, 0);
                izq.addTerm(u_oi, listaW1[o]);
            }
            for (int a = 0; a < this.aisles.size(); a++) {
                int u_ai = this.aisles.get(a).getOrDefault(i, 0);
                der.addTerm(u_ai, listaA1[a]);
            }
            //izq < der + z
            der.addTerm(1, z); //Add z to der
            prob.addLe(izq, der); //Stock is upper bound of grabbed items for all i
        }

        //List all possible values of k
        Set<Double> conjValoresK = new HashSet<>();
        for (int b = waveSizeLB; b < waveSizeUB + 1; b++) {
            for (int a = 1; a <= aisles.size(); a++) {
                conjValoresK.add((double) b / a);
            }
        }
        // Convert Set a List
        List<Double> valoresK = new ArrayList<>(conjValoresK);
        Collections.sort(valoresK); // Ordenar la lista
        //We will run the binary search on the array, instead of taking an epsilon
        List<Boolean> valoresW = List.of();
        List<Boolean> valoresA = List.of();
        prob.addMinimize(z);
        prob.setParam(IloCplex.Param.MIP.Tolerances.AbsMIPGap, TOLERANCE);

        //The sum of aisles used by the model (defined outside the while loop)
        IloLinearNumExpr sumaDeA = prob.linearNumExpr();
        for (int a = 0; a < this.aisles.size(); a++) {
            sumaDeA.addTerm(1, listaA1[a]);
        }
        prob.addGe(sumaDeA, 1);

        //Set params for the binary search
        int searchMin = 0;
        int searchMax = valoresK.size();

        // Solve the model for the LB to have the worst case scenario
        IloConstraint restriccion1 = prob.addGe(prob.sum(prob.prod(valoresK.get(0), sumaDeA), prob.prod(-1, suma)), -EPSILON); // Convertirlo a restricciones ensanguchadas con epsilon
        IloConstraint restriccion2 = prob.addLe(prob.sum(prob.prod(valoresK.get(0), sumaDeA), prob.prod(-1, suma)), EPSILON - 10e-3);

        boolean isSolved = prob.solve();

        if (isSolved){
            valoresW = new ArrayList<>();
            valoresA = new ArrayList<>();

            for (IloIntVar w : listaW1) {
                valoresW.add(prob.getValue(w) >= 0.5);
            }

            for (IloIntVar a : listaA1) {
                valoresA.add(prob.getValue(a) >= 0.5);
            }
        }
        else{
            System.out.println(String.format("Infactible", 0));
            return null;
        }

        prob.remove(restriccion1);
        prob.remove(restriccion2);

        int remainingTime = (int) this.getRemainingTime(stopWatch);
        
        while (searchMin < searchMax - 1 && remainingTime > this.MAX_REMAINING_SECONDS_TO_STOP) { //Termination criterion
            prob.setParam(IloCplex.Param.TimeLimit, remainingTime-5);

            System.out.println(String.format("Remaining time: %d", remainingTime));
            int j = (int) Math.floor((double) (searchMax + searchMin) / 2);

            restriccion1 = prob.addGe(prob.sum(prob.prod(valoresK.get(j), sumaDeA), prob.prod(-1, suma)), -EPSILON); // Convertirlo a restricciones ensanguchadas con epsilon
            restriccion2 = prob.addLe(prob.sum(prob.prod(valoresK.get(j), sumaDeA), prob.prod(-1, suma)), EPSILON - 10e-3);

            isSolved = prob.solve();

            if (isSolved) {
                double z_obj = prob.getObjValue();
                if (z_obj > 0) {
                    searchMax = j;
                }
                else {
                    searchMin = j;
        
                    valoresW = new ArrayList<>();
                    valoresA = new ArrayList<>();

                    for (IloIntVar w : listaW1) {
                        valoresW.add(prob.getValue(w) >= 0.5);
                    }

                    for (IloIntVar a : listaA1) {
                        valoresA.add(prob.getValue(a) >= 0.5);
                    }
                }
            } else {
                return null;
            }

            prob.remove(restriccion1);
            prob.remove(restriccion2);
            remainingTime = (int) this.getRemainingTime(stopWatch);
        }

        resBB.add(valoresW);
        resBB.add(valoresA);
        return resBB;
    }
    /*
     * Get the remaining time in seconds
     */
    protected long getRemainingTime(StopWatch stopWatch) {
        return Math.max(
                TimeUnit.SECONDS.convert(MAX_RUNTIME - stopWatch.getTime(TimeUnit.MILLISECONDS), TimeUnit.MILLISECONDS),
                0);
    }

    protected boolean isSolutionFeasible(ChallengeSolution challengeSolution) {
        Set<Integer> selectedOrders = challengeSolution.orders();
        Set<Integer> visitedAisles = challengeSolution.aisles();
        if (selectedOrders == null || visitedAisles == null || selectedOrders.isEmpty() || visitedAisles.isEmpty()) {
            return false;
        }

        int[] totalUnitsPicked = new int[this.nItems];
        int[] totalUnitsAvailable = new int[this.nItems];

        // Calculate total units picked
        for (int order : selectedOrders) {
            for (Map.Entry<Integer, Integer> entry : orders.get(order).entrySet()) {
                totalUnitsPicked[entry.getKey()] += entry.getValue();
            }
        }

        // Calculate total units available
        for (int aisle : visitedAisles) {
            for (Map.Entry<Integer, Integer> entry : aisles.get(aisle).entrySet()) {
                totalUnitsAvailable[entry.getKey()] += entry.getValue();
            }
        }

        // Check if the total units picked are within bounds
        int totalUnits = Arrays.stream(totalUnitsPicked).sum();
        if (totalUnits < waveSizeLB || totalUnits > waveSizeUB) {
            return false;
        }

        // Check if the units picked do not exceed the units available
        for (int i = 0; i < nItems; i++) {
            if (totalUnitsPicked[i] > totalUnitsAvailable[i]) {
                return false;
            }
        }

        return true;
    }

    protected double computeObjectiveFunction(ChallengeSolution challengeSolution) {
        Set<Integer> selectedOrders = challengeSolution.orders();
        Set<Integer> visitedAisles = challengeSolution.aisles();
        if (selectedOrders == null || visitedAisles == null || selectedOrders.isEmpty() || visitedAisles.isEmpty()) {
            return 0.0;
        }
        int totalUnitsPicked = 0;

        // Calculate total units picked
        for (int order : selectedOrders) {
            totalUnitsPicked += orders.get(order).values().stream()
                    .mapToInt(Integer::intValue)
                    .sum();
        }

        // Calculate the number of visited aisles
        int numVisitedAisles = visitedAisles.size();

        // Objective function: total units picked / number of visited aisles
        return (double) totalUnitsPicked / numVisitedAisles;
    }
}

//java -jar target/ChallengeSBPO2025-1.0.jar datasets\a\instance_0001.txt ./outputs/outputs_01_approx_bis.txt