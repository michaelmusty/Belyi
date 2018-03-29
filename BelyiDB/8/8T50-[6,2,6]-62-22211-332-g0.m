s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,2,6]-62-22211-332-g0";
s`BelyiDBFilename := "8T50-[6,2,6]-62-22211-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 2, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 3, 2, 1, 8, 4, 6, 7 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 3, 4, 1, 5, 2, 7, 8, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 3, 2, 1, 8, 4, 6, 7 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 3, 4, 1, 5, 2, 7, 8, 6 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 3, 2, 1, 8, 4, 6, 7 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 3, 4, 1, 5, 2, 7, 8, 6 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 3, 2, 1, 8, 4, 6, 7 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 3, 4, 1, 5, 2, 7, 8, 6 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 7, 2, 8, 6, 5, 4, 1, 3 ],
[ 2, 8, 6, 5, 4, 7, 3, 1 ]
],
[ PermutationGroup<8 |  
\[ 5, 3, 2, 1, 8, 4, 6, 7 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 3, 4, 1, 5, 2, 7, 8, 6 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 7, 5, 3, 4, 2, 8, 1, 6 ],
[ 5, 3, 4, 2, 8, 7, 6, 1 ]
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
[ 5, 3, 2, 1, 8, 4, 6, 7 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 3, 4, 1, 5, 2, 7, 8, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 7, 5, 4, 2, 6, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
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
