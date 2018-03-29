s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,15,4]-611-53-41111-g0";
s`BelyiDBFilename := "8T50-[6,15,4]-611-53-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 15, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 5, 3, 4, 6, 7, 8, 1 ],
[ 4, 8, 1, 3, 2, 5, 6, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 5, 3, 4, 6, 7, 8, 1 ],
\[ 4, 8, 1, 3, 2, 5, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 5, 3, 4, 6, 7, 8, 1 ],
\[ 4, 8, 1, 3, 2, 5, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 5, 3, 4, 6, 7, 8, 1 ],
\[ 4, 8, 1, 3, 2, 5, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 7, 1, 3, 4, 5, 8, 2 ],
[ 1, 3, 8, 4, 5, 6, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 3, 4, 6, 7, 8, 1 ],
\[ 4, 8, 1, 3, 2, 5, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 7, 2, 8, 4, 5, 3, 1 ],
[ 1, 8, 3, 7, 5, 6, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 3, 4, 6, 7, 8, 1 ],
\[ 4, 8, 1, 3, 2, 5, 6, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 4, 2, 3, 7, 5, 8, 1 ],
[ 1, 8, 3, 4, 2, 6, 5, 7 ]
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
[ 2, 5, 3, 4, 6, 7, 8, 1 ],
[ 4, 8, 1, 3, 2, 5, 6, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 5, 3, 4, 6, 1, 8, 2 ],
[ 4, 6, 8, 3, 2, 5, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 5, 3, 6, 7, 1, 8 ],
[ 8, 7, 2, 1, 3, 5, 6, 4 ],
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
