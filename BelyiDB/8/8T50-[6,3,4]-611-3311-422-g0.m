s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,3,4]-611-3311-422-g0";
s`BelyiDBFilename := "8T50-[6,3,4]-611-3311-422-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 8, 3, 1, 5, 4, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 6, 3, 2, 5, 4, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 3, 2, 5, 4, 1, 7, 8, 6 ],
[ 2, 1, 4, 3, 8, 5, 6, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 1, 2, 6, 7, 4, 8, 5, 3 ],
[ 2, 8, 5, 7, 3, 1, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 6, 2, 5, 4, 8, 7, 1, 3 ],
[ 2, 8, 4, 3, 1, 7, 6, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 6, 8, 2, 4, 5, 7, 1, 3 ],
[ 3, 8, 4, 5, 1, 7, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 8, 3, 1, 5, 4, 6, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 8, 1, 5, 4, 7, 6, 3, 2 ],
[ 8, 7, 4, 3, 6, 2, 5, 1 ]
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
[ 2, 8, 3, 1, 5, 4, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 6, 3, 2, 5, 4, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 8, 5, 3, 6, 1, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 7, 1, 4, 3, 6, 5, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 2, 1, 8, 5, 3, 4, 6 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 2, 1, 5, 7, 4, 8, 3, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 7, 8, 4, 5, 3, 1, 2 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 7, 8, 5, 6, 4, 3, 1, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 1, 8, 5, 7, 3, 6 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 2, 1, 7, 3, 4, 8, 5, 6 ]
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
