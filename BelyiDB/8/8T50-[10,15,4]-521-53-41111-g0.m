s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[10,15,4]-521-53-41111-g0";
s`BelyiDBFilename := "8T50-[10,15,4]-521-53-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 10, 15, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 4, 2, 5, 1, 7, 6, 8 ],
[ 8, 5, 1, 2, 4, 7, 3, 6 ],
[ 2, 7, 3, 4, 5, 6, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 6, 8 ],
[ 8, 1, 7, 3, 4, 5, 6, 2 ],
[ 6, 2, 8, 4, 5, 3, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 6, 8 ],
[ 3, 1, 2, 8, 4, 5, 6, 7 ],
[ 6, 2, 3, 1, 5, 8, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 6, 8 ],
[ 5, 4, 2, 3, 6, 7, 8, 1 ],
[ 1, 8, 3, 4, 2, 6, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 2, 5, 1, 7, 6, 8 ],
\[ 8, 5, 1, 2, 4, 7, 3, 6 ],
\[ 2, 7, 3, 4, 5, 6, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 6, 8 ],
[ 8, 1, 2, 3, 6, 7, 5, 4 ],
[ 7, 2, 3, 4, 8, 6, 5, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 4, 2, 5, 1, 7, 6, 8 ],
[ 8, 5, 1, 2, 4, 7, 3, 6 ],
[ 2, 7, 3, 4, 5, 6, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 2, 4, 5, 6, 1, 8, 7 ],
[ 7, 6, 2, 3, 4, 5, 8, 1 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 4, 2, 5, 1, 8, 7, 6 ],
[ 6, 5, 1, 2, 4, 8, 3, 7 ],
[ 2, 7, 3, 4, 5, 6, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 2, 5, 3, 1, 4, 8, 7 ],
[ 7, 5, 2, 6, 3, 1, 8, 4 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
