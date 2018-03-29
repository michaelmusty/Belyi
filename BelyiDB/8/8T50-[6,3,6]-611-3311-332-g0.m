s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,3,6]-611-3311-332-g0";
s`BelyiDBFilename := "8T50-[6,3,6]-611-3311-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 7, 4, 2, 5, 1, 6, 8 ],
[ 2, 8, 4, 5, 3, 6, 7, 1 ],
[ 6, 3, 8, 5, 4, 7, 1, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 3, 2, 8, 4, 6, 7, 5, 1 ],
[ 5, 8, 2, 1, 4, 7, 6, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 2, 8, 3, 6, 5, 7, 4, 1 ],
[ 4, 8, 1, 3, 7, 5, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 3, 2, 8, 7, 5, 4, 6, 1 ],
[ 7, 8, 2, 1, 6, 5, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 7, 4, 2, 5, 1, 6, 8 ],
\[ 2, 8, 4, 5, 3, 6, 7, 1 ],
\[ 6, 3, 8, 5, 4, 7, 1, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 2, 8, 7, 4, 5, 3, 6, 1 ],
[ 7, 8, 1, 6, 4, 5, 3, 2 ]
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
[ 3, 7, 4, 2, 5, 1, 6, 8 ],
[ 2, 8, 4, 5, 3, 6, 7, 1 ],
[ 6, 3, 8, 5, 4, 7, 1, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 6, 1, 4, 3, 5, 2, 8 ],
[ 2, 8, 4, 5, 3, 6, 7, 1 ],
[ 5, 7, 4, 3, 6, 1, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 5, 6, 4, 3, 1, 2, 8 ],
[ 2, 8, 4, 5, 3, 6, 7, 1 ],
[ 6, 7, 4, 3, 1, 5, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 3, 4, 7, 2, 6, 1 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ],
[ 8, 5, 2, 6, 3, 7, 4, 1 ]
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
