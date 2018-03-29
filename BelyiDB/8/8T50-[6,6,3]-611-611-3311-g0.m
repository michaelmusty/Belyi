s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,6,3]-611-611-3311-g0";
s`BelyiDBFilename := "8T50-[6,6,3]-611-611-3311-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 1, 4, 7, 5, 6, 8, 2 ],
[ 1, 2, 8, 6, 3, 5, 4, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 1, 4, 7, 5, 6, 8, 2 ],
\[ 1, 2, 8, 6, 3, 5, 4, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 1, 4, 7, 5, 6, 8, 2 ],
\[ 1, 2, 8, 6, 3, 5, 4, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 1, 4, 7, 5, 6, 8, 2 ],
\[ 1, 2, 8, 6, 3, 5, 4, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 7, 3, 4, 2, 5, 8, 1 ],
[ 1, 8, 5, 3, 4, 6, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 7, 5, 6, 8, 2 ],
\[ 1, 2, 8, 6, 3, 5, 4, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 4, 7, 2, 3, 5, 6, 8, 1 ],
[ 6, 8, 3, 4, 1, 5, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 4, 7, 5, 6, 8, 2 ],
\[ 1, 2, 8, 6, 3, 5, 4, 7 ],
\[ 2, 3, 1, 5, 6, 4, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 1, 7, 2, 3, 5, 8, 6, 4 ],
[ 7, 1, 3, 4, 8, 5, 2, 6 ]
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
[ 3, 1, 4, 7, 5, 6, 8, 2 ],
[ 1, 2, 8, 6, 3, 5, 4, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 2, 3, 6, 4, 7, 8, 1 ],
[ 3, 8, 2, 4, 5, 1, 6, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 1, 3, 4, 7, 5, 8, 2 ],
[ 3, 2, 8, 1, 4, 6, 5, 7 ],
[ 2, 3, 1, 5, 6, 4, 7, 8 ]
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
