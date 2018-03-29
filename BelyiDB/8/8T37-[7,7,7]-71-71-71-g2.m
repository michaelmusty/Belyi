s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T37-[7,7,7]-71-71-71-g2";
s`BelyiDBFilename := "8T37-[7,7,7]-71-71-71-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 7, 7 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 168 > |
[ 2, 3, 4, 5, 6, 8, 7, 1 ],
[ 2, 7, 1, 3, 6, 4, 5, 8 ],
[ 8, 3, 1, 4, 6, 7, 2, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 7, 1, 3, 6, 4, 5, 8 ],
\[ 8, 3, 1, 4, 6, 7, 2, 5 ]:
 Order := 168 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 7, 1, 3, 6, 4, 5, 8 ],
\[ 8, 3, 1, 4, 6, 7, 2, 5 ]:
 Order := 168 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 7, 1, 3, 6, 4, 5, 8 ],
\[ 8, 3, 1, 4, 6, 7, 2, 5 ]:
 Order := 168 > |
[ 2, 3, 4, 5, 6, 8, 7, 1 ],
[ 2, 8, 3, 5, 7, 4, 1, 6 ],
[ 2, 7, 1, 3, 6, 4, 5, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 168 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 168 > |
[ 2, 3, 4, 5, 6, 8, 7, 1 ],
[ 2, 7, 1, 3, 6, 4, 5, 8 ],
[ 8, 3, 1, 4, 6, 7, 2, 5 ]
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
